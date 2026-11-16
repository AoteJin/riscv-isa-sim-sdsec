// SPDX-License-Identifier: BSD-3-Clause
// Processor-level trigger delegation regressions. CSR accesses check permissions.
#include "processor.h"
#include "simif.h"
#include "csrs.h"
#include "debug_defines.h"
#include "trap.h"
#include <array>
#include <cstring>
#include <cstdlib>
#include <iostream>
#include <map>
#include <stdexcept>
#include <string>

struct minimal_sim : simif_t {
  cfg_t cfg;
  std::map<size_t, processor_t*> harts;
  char* addr_to_mem(reg_t) override { return nullptr; }
  bool mmio_load(reg_t, size_t, uint8_t*) override { return false; }
  bool mmio_store(reg_t, size_t, const uint8_t*) override { return false; }
  void proc_reset(unsigned) override {}
  const cfg_t& get_cfg() const override { return cfg; }
  const std::map<size_t, processor_t*>& get_harts() const override { return harts; }
  const char* get_symbol(uint64_t) override { return nullptr; }
};

unsigned checks = 0, failures = 0;
void check(const std::string& label, reg_t actual, reg_t expected) {
  ++checks;
  failures += actual != expected;
  std::cout << (actual == expected ? "PASS " : "FAIL ") << label
            << " actual=0x" << std::hex << actual << " expected=0x" << expected
            << std::dec << '\n';
}
void require_setup(bool ok, const char* msg) {
  if (!ok) throw std::runtime_error(msg);
}
reg_t read_csr(processor_t& p, unsigned csr) {
  // Use an actual CSRRS encoding and explicitly disable the API's default peek.
  return p.get_csr(csr, insn_t((reg_t(csr) << 20) | 0x2073), false, false);
}
void write_csr(processor_t& p, unsigned csr, reg_t value) {
  // put_csr alone bypasses permissions: verify as CSRRW before mutating.
  p.get_csr(csr, insn_t((reg_t(csr) << 20) | 0x1073), true, false);
  p.put_csr(csr, value);
}
reg_t type_value(unsigned type) { return reg_t(type) << CSR_TDATA1_TYPE_OFFSET(64); }

void check_access_matrix(processor_t& p) {
  auto reset = [&]() {
    p.set_privilege(PRV_M, false);
    p.put_csr(CSR_MSTATEEN0, ~reg_t(0));
    p.put_csr(CSR_HSTATEEN0, ~reg_t(0));
    p.put_csr(CSR_SSTATEEN0, ~reg_t(0));
    p.put_csr(CSR_UISELECT, UISELECT_TRIG);
    p.put_csr(CSR_SISELECT, SISELECT_TRIG);
    p.put_csr(CSR_VSISELECT, VSISELECT_TRIG);
  };
  auto expect = [&](const std::string& label, unsigned csr, reg_t cause) {
    reg_t actual = 0;
    try { read_csr(p, csr); } catch (trap_t& t) { actual = t.cause(); }
    check(label, actual, cause);
  };
  struct Case { const char* name; reg_t bit; unsigned csr; unsigned prv; bool v; };
  const Case cases[] = {
    {"TR HS alias", MSTATEEN0_TR, CSR_SIREG, PRV_S, false},
    {"TR VS alias", MSTATEEN0_TR, CSR_SIREG, PRV_S, true},
    {"TR U alias", MSTATEEN0_TR, CSR_UIREG, PRV_U, false},
    {"TR VU alias", MSTATEEN0_TR, CSR_UIREG, PRV_U, true},
    {"UCSRIND HS select", MSTATEEN0_UCSRIND, CSR_UISELECT, PRV_S, false},
    {"UCSRIND VS select", MSTATEEN0_UCSRIND, CSR_UISELECT, PRV_S, true},
    {"UCSRIND U alias", MSTATEEN0_UCSRIND, CSR_UIREG, PRV_U, false},
    {"UCSRIND VU alias", MSTATEEN0_UCSRIND, CSR_UIREG, PRV_U, true}
  };
  for (auto c: cases) {
    reset(); p.set_privilege(c.prv, c.v); expect(std::string(c.name)+" enabled", c.csr, 0);
    reset(); p.put_csr(CSR_MSTATEEN0, ~c.bit); p.set_privilege(c.prv,c.v);
    expect(std::string(c.name)+" machine denies", c.csr, CAUSE_ILLEGAL_INSTRUCTION);
    if (c.v) {
      reset(); p.put_csr(CSR_HSTATEEN0, ~c.bit); p.set_privilege(c.prv,c.v);
      expect(std::string(c.name)+" hypervisor denies", c.csr, CAUSE_VIRTUAL_INSTRUCTION);
    }
    if (c.prv==PRV_U) {
      reset(); p.put_csr(CSR_SSTATEEN0, ~c.bit); p.set_privilege(c.prv,c.v);
      expect(std::string(c.name)+" supervisor denies", c.csr, c.v ? CAUSE_VIRTUAL_INSTRUCTION : CAUSE_ILLEGAL_INSTRUCTION);
    }
  }
  reset(); p.put_csr(CSR_MSTATEEN0, ~MSTATEEN0_CSRIND); p.set_privilege(PRV_U,false);
  expect("user alias independent of CSRIND",CSR_UIREG,0);
  reset();
  p.get_state()->debug_mode=true;
  p.put_csr(CSR_TDATA1,type_value(CSR_TDATA1_TYPE_MCONTROL6)|CSR_MCONTROL6_DMODE(64));
  p.put_csr(CSR_TDATA2,0x12345678);
  p.get_state()->debug_mode=false;
  struct Mode { const char* name; unsigned prv; bool v; unsigned csr; };
  const Mode modes[]={{"M",PRV_M,false,CSR_SIREG2},{"HS",PRV_S,false,CSR_SIREG2},{"VS",PRV_S,true,CSR_SIREG2},{"U",PRV_U,false,CSR_UIREG2},{"VU",PRV_U,true,CSR_UIREG2}};
  for (auto mode:modes) for (reg_t policy:{reg_t(0),reg_t(1),reg_t(2),reg_t(4)}) {
    reset(); p.put_csr(CSR_TDATA2,0x12345678); p.put_csr(CSR_MDTCFG,policy); p.set_privilege(mode.prv,mode.v);
    bool allowed=mode.prv==PRV_M || (mode.prv==PRV_S && !(policy&1) && (!mode.v || !(policy&6)));
    check(std::string("DMODE ")+mode.name+" policy="+std::to_string(policy),read_csr(p,mode.csr),allowed?0x12345678:0);
    write_csr(p,mode.csr,0x87654321);
    p.set_privilege(PRV_M,false);
    check(std::string("DMODE write ")+mode.name+" policy="+std::to_string(policy),read_csr(p,CSR_TDATA2),allowed?0x87654321:0x12345678);
  }
}

void check_user_only_configuration(const char* isa, unsigned xlen) {
  minimal_sim sim;
  sim.cfg.trigger_count = 2;
  processor_t p(isa, "MU", &sim.cfg, &sim, 0, false, stderr, std::cerr);
  sim.harts[0] = &p;
  const std::string label = std::string("RV") + std::to_string(xlen) + " no-S ";
  p.put_csr(CSR_MSTATEEN0, MSTATEEN0_TR | MSTATEEN0_UCSRIND);
  p.put_csr(CSR_UISELECT, UISELECT_TRIG);
  for (unsigned index : {0U, 1U}) {
    p.set_privilege(PRV_U, false);
    write_csr(p, CSR_UIREG5, index);
    check(label + "selection", read_csr(p, CSR_UIREG5), index);
    write_csr(p, CSR_UIREG, (reg_t(CSR_TDATA1_TYPE_MCONTROL6) << (xlen - 4)) |
              CSR_MCONTROL6_M | CSR_MCONTROL6_S | CSR_MCONTROL6_U);
    write_csr(p, CSR_UIREG2, 0x12340000 + index);
    const reg_t modes = read_csr(p, CSR_UIREG) &
      (CSR_MCONTROL6_M | CSR_MCONTROL6_S | CSR_MCONTROL6_U);
    check(label + "user mode mapping", modes, CSR_MCONTROL6_U);
  }
  for (unsigned index : {0U, 1U}) {
    write_csr(p, CSR_UIREG5, index);
    check(label + "independent trigger data", read_csr(p, CSR_UIREG2), 0x12340000 + index);
  }
  write_csr(p, CSR_UISELECT, 0xfff);
  check(label + "selector minimum range", read_csr(p, CSR_UISELECT), 0xfff);
  p.set_privilege(PRV_M, false);
  p.put_csr(CSR_MDTCFG, MDTCFG_VUEDBGALW);
  check(label + "absent VU control is zero", read_csr(p, CSR_MDTCFG), 0);
  p.put_csr(CSR_MSTATEEN0, MSTATEEN0_UCSRIND);
  p.set_privilege(PRV_U, false);
  write_csr(p, CSR_UISELECT, UISELECT_TRIG);
  reg_t cause = 0;
  try { read_csr(p, CSR_UIREG); } catch (trap_t& t) { cause = t.cause(); }
  check(label + "TR denial without S", cause, CAUSE_ILLEGAL_INSTRUCTION);
}

void check_debug_privileges(processor_t& p) {
  struct Case { reg_t policy; bool guest; unsigned privilege; bool virtualized; };
  const Case cases[] = {
    {1, false, PRV_S, false}, {1, true, PRV_S, false},
    {2, true, PRV_S, true}, {4, false, PRV_U, false},
    {8, true, PRV_U, true}, {6, false, PRV_U, false},
    {6, true, PRV_S, true}, {10, true, PRV_S, true}
  };
  for (auto c : cases) {
    p.set_privilege(PRV_M, false);
    p.put_csr(CSR_MDTCFG, c.policy);
    p.get_state()->dcsr->v = c.guest;
    p.set_debug_privilege();
    const std::string label = "debug privilege policy=" + std::to_string(c.policy) +
      (c.guest ? " guest" : " physical");
    check(label + " privilege", p.get_state()->prv, c.privilege);
    check(label + " virtualization", p.get_state()->v, c.virtualized);
  }
}

void check_field_mappings(processor_t& p) {
  struct Type { unsigned type; reg_t m, s, u, vs, vu; };
  const Type types[] = {
    {6, CSR_MCONTROL6_M, CSR_MCONTROL6_S, CSR_MCONTROL6_U, CSR_MCONTROL6_VS, CSR_MCONTROL6_VU},
    {3, CSR_ICOUNT_M, CSR_ICOUNT_S, CSR_ICOUNT_U, CSR_ICOUNT_VS, CSR_ICOUNT_VU},
    {4, CSR_ITRIGGER_M, CSR_ITRIGGER_S, CSR_ITRIGGER_U, CSR_ITRIGGER_VS, CSR_ITRIGGER_VU},
    {5, CSR_ETRIGGER_M, CSR_ETRIGGER_S, CSR_ETRIGGER_U, CSR_ETRIGGER_VS, CSR_ETRIGGER_VU}
  };
  struct View { const char* name; unsigned privilege; bool guest; unsigned csr; };
  const View views[] = {{"S", PRV_S, false, CSR_SIREG}, {"VS", PRV_S, true, CSR_SIREG},
                        {"U", PRV_U, false, CSR_UIREG}, {"VU", PRV_U, true, CSR_UIREG}};
  p.set_privilege(PRV_M, false);
  p.put_csr(CSR_MSTATEEN0, ~reg_t(0));
  p.put_csr(CSR_HSTATEEN0, ~reg_t(0));
  p.put_csr(CSR_SSTATEEN0, ~reg_t(0));
  p.put_csr(CSR_SISELECT, SISELECT_TRIG);
  p.put_csr(CSR_VSISELECT, VSISELECT_TRIG);
  p.put_csr(CSR_UISELECT, UISELECT_TRIG);
  p.put_csr(CSR_TSELECT, 0);
  for (auto type : types) for (auto view : views) {
    if (view.privilege == PRV_U && type.type != 6 && type.type != 3) continue;
    const reg_t mask = type.m | type.s | type.u | type.vs | type.vu;
    const std::string label = std::string(view.name) + " type=" + std::to_string(type.type);
    for (bool first : {true, false}) {
      p.set_privilege(PRV_M, false);
      p.put_csr(CSR_TDATA1, type_value(15));
      // Contrasting native S/U and VS/VU patterns distinguish read mapping.
      reg_t native = first ? type.s | type.vu : type.u | type.vs;
      p.put_csr(CSR_TDATA1, type_value(type.type) | native | type.m);
      p.set_privilege(view.privilege, view.guest);
      reg_t expected = 0;
      if (view.privilege == PRV_S && !view.guest) expected = native;
      if (view.privilege == PRV_S && view.guest) expected = first ? type.u : type.s;
      if (view.privilege == PRV_U) expected = (view.guest ? first : !first) ? type.u : 0;
      check(label + " native to alias", read_csr(p, view.csr) & mask, expected);

      p.set_privilege(PRV_M, false);
      p.put_csr(CSR_TDATA1, type_value(15));
      p.put_csr(CSR_TDATA1, type_value(type.type));
      p.set_privilege(view.privilege, view.guest);
      reg_t input = first ? type.s : type.u;
      reg_t output = input;
      if (view.privilege == PRV_S && !view.guest) input |= type.m;
      if (view.privilege == PRV_S && view.guest) {
        input |= type.m | type.vs | type.vu;
        output = first ? type.vs : type.vu;
      }
      if (view.privilege == PRV_U) {
        input = type.m | type.s | type.vs | type.vu | (first ? type.u : 0);
        output = first ? (view.guest ? type.vu : type.u) : 0;
      }
      write_csr(p, view.csr, type_value(type.type) | input);
      p.set_privilege(PRV_M, false);
      reg_t actual = read_csr(p, CSR_TDATA1);
      check(label + " alias to native", actual & mask, output);
      check(label + " native type retained", actual >> 60, type.type);
    }
  }
}

void check_textra(const char* isa, unsigned xlen) {
  minimal_sim sim;
  processor_t p(isa, "MSU", &sim.cfg, &sim, 0, false, stderr, std::cerr);
  sim.harts[0] = &p;
  p.put_csr(CSR_MSTATEEN0, ~reg_t(0));
  if (xlen == 32) p.put_csr(CSR_MSTATEEN0H, ~reg_t(0));
  if (p.extension_enabled('H')) p.put_csr(CSR_HSTATEEN0, ~reg_t(0));
  p.put_csr(CSR_SSTATEEN0, ~reg_t(0));
  p.put_csr(CSR_SISELECT, SISELECT_TRIG);
  if (p.extension_enabled('H')) p.put_csr(CSR_VSISELECT, VSISELECT_TRIG);
  p.put_csr(CSR_UISELECT, UISELECT_TRIG);
  p.put_csr(CSR_TDATA1, reg_t(6) << (xlen - 4));
  reg_t mh = xlen == 32 ? CSR_TEXTRA32_MHVALUE | CSR_TEXTRA32_MHSELECT :
                         CSR_TEXTRA64_MHVALUE | CSR_TEXTRA64_MHSELECT;
  reg_t seed = (reg_t(1) << (xlen == 32 ? 26 : 51)) |
               (reg_t(4) << (xlen == 32 ? 23 : 48)) |
               (reg_t(1) << (xlen == 32 ? 18 : 36)) | (0x55 << 2) | 1;
  p.put_csr(CSR_TDATA3, seed);
  reg_t native = read_csr(p, CSR_TDATA3);
  const std::string label = "RV" + std::to_string(xlen) + " textra ";
  check(label + "native machine fields nonzero", (native & mh) != 0, 1);
  check(label + "native supervisor fields nonzero", (native & ~mh) != 0, 1);
  p.set_privilege(PRV_S, false);
  check(label + "S view unchanged", read_csr(p, CSR_SIREG3), native);
  if (p.extension_enabled('H')) {
    p.set_privilege(PRV_S, true);
    check(label + "VS read filters machine fields", read_csr(p, CSR_SIREG3), native & ~mh);
    p.set_privilege(PRV_M, false);
    p.put_csr(CSR_TDATA3, 0);
    p.set_privilege(PRV_S, true);
    write_csr(p, CSR_SIREG3, seed);
    p.set_privilege(PRV_M, false);
    check(label + "VS write retains supervisor fields", read_csr(p, CSR_TDATA3) & ~mh, native & ~mh);
    check(label + "VS write masks machine fields", read_csr(p, CSR_TDATA3) & mh, 0);
  }
  for (bool guest : {false, true}) {
    if (guest && !p.extension_enabled('H')) continue;
    p.set_privilege(PRV_M, false);
    p.put_csr(CSR_TDATA3, seed);
    p.set_privilege(PRV_U, guest);
    check(label + "user read is zero", read_csr(p, CSR_UIREG3), 0);
    write_csr(p, CSR_UIREG3, 0);
    p.set_privilege(PRV_M, false);
    check(label + "user write leaves native state unchanged", read_csr(p, CSR_TDATA3), native);
  }
}

void check_executed_self_hosted_trigger() {
  struct instruction_sim : minimal_sim {
    alignas(4096) std::array<uint8_t, 0x4000> memory{};
    char* addr_to_mem(reg_t address) override {
      if (address >= 0x80000000 && address < 0x80004000)
        return reinterpret_cast<char*>(memory.data() + address - 0x80000000);
      return nullptr;
    }
  } sim;
  const uint32_t nop = 0x00000013;
  std::memcpy(sim.memory.data() + 0x1000, &nop, sizeof(nop));
  std::memcpy(sim.memory.data() + 0x2000, &nop, sizeof(nop));
  processor_t p("rv64imac_sdsec", "MSU", &sim.cfg, &sim, 0, false, stderr, std::cerr);
  sim.harts[0] = &p;
  p.put_csr(CSR_PMPADDR0, ~reg_t(0));
  p.put_csr(CSR_PMPCFG0, 0x1f);
  p.put_csr(CSR_TDATA1, type_value(15));
  p.put_csr(CSR_MSTATEEN0, MSTATEEN0_TR | MSTATEEN0_UCSRIND);
  p.put_csr(CSR_SSTATEEN0, SSTATEEN0_TR | SSTATEEN0_UCSRIND);
  p.put_csr(CSR_UISELECT, UISELECT_TRIG);
  p.put_csr(CSR_MEDELEG, 0);
  p.put_csr(CSR_MTVEC, 0x80002000);
  p.set_privilege(PRV_U, false);
  write_csr(p, CSR_UIREG, type_value(6) | CSR_MCONTROL6_U | CSR_MCONTROL6_EXECUTE);
  write_csr(p, CSR_UIREG2, 0x80001000);
  check("executed self-hosted control: external debug disabled", p.is_debug_allowed(PRV_U, false), 0);
  p.get_state()->pc = 0x80001000;
  p.step(1);
  check("executed self-hosted breakpoint cause", read_csr(p, CSR_MCAUSE), CAUSE_BREAKPOINT);
  check("executed self-hosted breakpoint EPC", read_csr(p, CSR_MEPC), 0x80001000);
  check("executed self-hosted handler privilege", p.get_state()->prv, PRV_M);
  check("executed self-hosted handler instruction", p.get_state()->pc, 0x80002004);
  check("executed self-hosted exception avoids Debug Mode", p.get_state()->debug_mode, 0);
}

int main() {
  try {
    setenv("RISCV_MDBGEN_INIT", "0", 1);
    setenv("RISCV_MDTCFG_INIT", "0", 1);
    minimal_sim sim;
    sim.cfg.trigger_count = 1;
    processor_t p("rv64imafdch_sdsec", "MSU", &sim.cfg, &sim, 0, false, stderr, std::cerr);
    sim.harts[0] = &p;
    auto* s = p.get_state();
    require_setup(p.extension_enabled(EXT_SUTCFG), "Sutcfg missing: stale library?");
    require_setup(p.extension_enabled('H'), "H missing");
    p.put_csr(CSR_MSTATEEN0, ~reg_t(0));
    p.put_csr(CSR_HSTATEEN0, ~reg_t(0));
    p.put_csr(CSR_SSTATEEN0, ~reg_t(0));
    p.put_csr(CSR_SISELECT, SISELECT_TRIG);
    p.put_csr(CSR_VSISELECT, VSISELECT_TRIG);
    p.put_csr(CSR_UISELECT, UISELECT_TRIG);

    std::cout << "=== INTRODUCED: unsupported selected type must hide tinfo ===\n";
    for (unsigned type : {CSR_TDATA1_TYPE_ITRIGGER, CSR_TDATA1_TYPE_ETRIGGER}) {
      p.set_privilege(PRV_M, false);
      p.put_csr(CSR_TDATA1, type_value(type));
      require_setup((p.get_csr(CSR_TDATA1) >> 60) == type, "native trigger type setup failed");
      p.set_privilege(PRV_U, false);
      check("U type=" + std::to_string(type) + " uireg", read_csr(p, CSR_UIREG), 0);
      check("U type=" + std::to_string(type) + " uireg4/tinfo", read_csr(p, CSR_UIREG4), 0);
    }
    p.set_privilege(PRV_M, false);
    p.put_csr(CSR_TDATA1, type_value(CSR_TDATA1_TYPE_MCONTROL));
    require_setup((p.get_csr(CSR_TDATA1) >> 60) == CSR_TDATA1_TYPE_MCONTROL, "mcontrol setup failed");
    p.set_privilege(PRV_S, false);
    check("HS mcontrol sireg", read_csr(p, CSR_SIREG), 0);
    check("HS mcontrol sireg4/tinfo", read_csr(p, CSR_SIREG4), 0);
    p.set_privilege(PRV_S, true);
    check("VS mcontrol sireg4/tinfo (virtualized)", read_csr(p, CSR_SIREG4), 0);
    p.set_privilege(PRV_M, false);
    p.put_csr(CSR_TDATA1, type_value(CSR_TDATA1_TYPE_DISABLED));
    p.set_privilege(PRV_U, false);
    check("control: supported disabled type exposes tinfo", read_csr(p, CSR_UIREG4) != 0, 1);

    std::cout << "=== BASELINE: ACTION=0 must work with external debug disabled ===\n";
    // Configure through the actual delegated user interface; no machine trigger writes.
    p.set_privilege(PRV_M, false);
    p.put_csr(CSR_MDTCFG, 0);
    p.put_csr(CSR_MEDELEG, 0); // breakpoint goes to M, so no SIE inhibition applies in U.
    p.set_privilege(PRV_U, false);
    write_csr(p, CSR_UIREG, type_value(CSR_TDATA1_TYPE_MCONTROL6) |
                               CSR_MCONTROL6_U | CSR_MCONTROL6_EXECUTE);
    write_csr(p, CSR_UIREG2, 0x80001000);
    const reg_t programmed = read_csr(p, CSR_UIREG);
    require_setup((programmed >> 60) == CSR_TDATA1_TYPE_MCONTROL6 &&
                  (programmed & CSR_MCONTROL6_U) && (programmed & CSR_MCONTROL6_EXECUTE) &&
                  !(programmed & CSR_MCONTROL6_ACTION) && !(programmed & CSR_MCONTROL6_DMODE(64)),
                  "delegated ACTION=0 trigger configuration failed");
    check("control: tdata2 address configured", read_csr(p, CSR_UIREG2), 0x80001000);
    check("control: external debug initially disabled", p.is_debug_allowed(PRV_U, false), 0);
    auto match = [&]() {
      auto result = p.TM.detect_memory_access_match(triggers::OPERATION_EXECUTE, 0x80001000, std::nullopt);
      if (result) require_setup(result->action == triggers::ACTION_DEBUG_EXCEPTION, "wrong action");
      return result.has_value();
    };
    check("ACTION=0 with external debug disabled", match(), 1);
    p.set_privilege(PRV_M, false);
    p.put_csr(CSR_MDTCFG, 0x4);
    p.set_privilege(PRV_U, false);
    check("control: same ACTION=0 trigger with U debug enabled", match(), 1);
    p.set_privilege(PRV_M, false);
    p.put_csr(CSR_MDTCFG, 0);
    p.set_privilege(PRV_U, false);
    check("ACTION=0 after external debug disabled again", match(), 1);

    std::cout << "=== BASELINE: independent U/VU permission matrix ===\n";
    for (reg_t policy : {reg_t(0), reg_t(4), reg_t(8), reg_t(12)}) {
      p.set_privilege(PRV_M, false);
      p.put_csr(CSR_MDTCFG, policy);
      const auto stored = p.get_csr(CSR_MDTCFG);
      std::cout << "policy requested=0x" << std::hex << policy << " stored=0x" << stored << std::dec << '\n';
      check("policy=" + std::to_string(policy) + " mdtcfg retention", stored, policy);
      check("policy=" + std::to_string(policy) + " U permission", p.is_debug_allowed(PRV_U, false), !!(policy & 4));
      check("policy=" + std::to_string(policy) + " VU permission", p.is_debug_allowed(PRV_U, true), !!(policy & 8));
    }
    check_access_matrix(p);
    check_executed_self_hosted_trigger();
    check_field_mappings(p);
    check_textra("rv64imafdch_sdsec", 64);
    check_textra("rv32imac_sdsec", 32);
    check_debug_privileges(p);
    check_user_only_configuration("rv32imac_sdsec", 32);
    check_user_only_configuration("rv64imac_sdsec", 64);
    std::cout << "SUMMARY checks=" << checks << " failures=" << failures << '\n';
    return failures ? 1 : 0;
  } catch (trap_t& t) {
    std::cerr << "HARNESS ERROR unexpected trap: " << t.name() << '\n';
    return 2;
  } catch (const std::exception& e) {
    std::cerr << "HARNESS ERROR " << e.what() << '\n';
    return 2;
  }
}
