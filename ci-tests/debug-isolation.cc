// SPDX-License-Identifier: BSD-3-Clause
// Adversarial tests of the specification's software isolation procedures.
#include "processor.h"
#include "simif.h"
#include "csrs.h"
#include "debug_defines.h"
#include "mmu.h"
#include <array>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <map>
#include <stdexcept>
#include <string>

namespace {
constexpr reg_t base = 0x80000000;
constexpr reg_t victim = base + 0x4000;
constexpr reg_t handler = base + 0x8000;
constexpr reg_t disabled = reg_t(15) << 60;
constexpr reg_t type6 = reg_t(6) << 60;
unsigned checks = 0, failures = 0;

void check(const std::string& label, reg_t actual, reg_t expected) {
  ++checks;
  failures += actual != expected;
  std::cout << (actual == expected ? "PASS " : "FAIL ") << label
            << " actual=0x" << std::hex << actual << " expected=0x" << expected
            << std::dec << '\n';
}

void require(bool value, const char* message) {
  if (!value) throw std::runtime_error(message);
}

struct memory_sim : simif_t {
  cfg_t cfg;
  std::map<size_t, processor_t*> harts;
  alignas(4096) std::array<uint8_t, 0x10000> memory{};
  alignas(4096) std::array<uint8_t, 0x1000> debug_rom{};
  memory_sim() {
    cfg.trigger_count = 2;
    const uint32_t nop = 0x00000013;
    for (size_t i = 0; i < memory.size(); i += 4)
      std::memcpy(memory.data() + i, &nop, 4);
    for (size_t i = 0; i < debug_rom.size(); i += 4)
      std::memcpy(debug_rom.data() + i, &nop, 4);
  }
  char* addr_to_mem(reg_t address) override {
    if (address >= base && address < base + memory.size())
      return reinterpret_cast<char*>(memory.data() + address - base);
    if (address < debug_rom.size())
      return reinterpret_cast<char*>(debug_rom.data() + address);
    return nullptr;
  }
  bool mmio_load(reg_t, size_t, uint8_t*) override { return false; }
  bool mmio_store(reg_t, size_t, const uint8_t*) override { return false; }
  void proc_reset(unsigned) override {}
  const cfg_t& get_cfg() const override { return cfg; }
  const std::map<size_t, processor_t*>& get_harts() const override { return harts; }
  const char* get_symbol(uint64_t) override { return nullptr; }
};

struct mode { unsigned privilege; bool guest; };
constexpr mode machine{PRV_M, false}, hs{PRV_S, false}, vs{PRV_S, true};
constexpr mode user{PRV_U, false}, vu{PRV_U, true};

// Manager boundaries are scheduled by the harness. CSR accesses and victim
// instructions execute in Spike; put_csr is used only for trusted boot setup.
struct fixture {
  memory_sim sim;
  processor_t p;
  reg_t instruction_pc = base + 0x1000;
  fixture() : p("rv64imafdch_sdsec", "MSU", &sim.cfg, &sim, 0, false, stderr, std::cerr) {
    sim.harts[0] = &p;
    p.put_csr(CSR_PMPADDR0, ~reg_t(0));
    p.put_csr(CSR_PMPCFG0, 0x1f);
    p.put_csr(CSR_MSTATEEN0, ~reg_t(0));
    p.put_csr(CSR_HSTATEEN0, ~reg_t(0));
    p.put_csr(CSR_SSTATEEN0, ~reg_t(0));
    p.put_csr(CSR_MTVEC, handler);
    p.put_csr(CSR_STVEC, handler);
    p.put_csr(CSR_VSTVEC, handler);
    p.put_csr(CSR_MEDELEG, 0);
    p.put_csr(CSR_HEDELEG, 0);
    p.put_csr(CSR_TDATA1, disabled);
    p.put_csr(CSR_TSELECT, 1);
    p.put_csr(CSR_TDATA1, disabled);
    p.put_csr(CSR_TSELECT, 0);
  }
  void context(mode m) {
    require(!p.get_state()->debug_mode, "unexpected Debug Mode at context boundary");
    p.set_privilege(m.privilege, m.guest);
  }
  void instruction(uint32_t bits) {
    require(instruction_pc < base + 0x3000, "instruction arena exhausted");
    reg_t pc = instruction_pc;
    instruction_pc += 4;
    std::memcpy(sim.memory.data() + pc - base, &bits, 4);
    p.get_mmu()->flush_icache();
    p.get_state()->pc = pc;
    p.step(1);
    require(p.get_state()->pc == pc + 4, "CSR instruction trapped or did not retire");
  }
  reg_t read(unsigned csr) {
    instruction((csr << 20) | (2 << 12) | (10 << 7) | 0x73);
    return p.get_state()->XPR[10];
  }
  void write(unsigned csr, reg_t value) {
    p.get_state()->XPR.write(11, value);
    instruction((csr << 20) | (11 << 15) | (1 << 12) | 0x73);
  }
  void policy(reg_t value) {
    context(machine);
    write(CSR_MDTCFG, value);
    check("policy write is effective", read(CSR_MDTCFG), value);
  }
  void enter_debug(mode child) {
    context(child);
    p.get_state()->pc = victim;
    p.halt_request = processor_t::HR_REGULAR;
    p.step(1);
    p.halt_request = processor_t::HR_NONE;
    require(p.get_state()->debug_mode, "debugger positive control denied entry");
    p.set_debug_privilege();
    require(p.get_state()->prv == child.privilege && p.get_state()->v == child.guest,
            "unexpected debug access privilege");
  }
  void leave_debug(mode child) {
    require(p.get_state()->debug_mode, "debugger was not active");
    // The scheduler models resume; this test does not test Debug Module transport.
    p.get_state()->debug_mode = false;
    context(child);
  }
  void arm(mode child, reg_t policy_value, bool self_hosted = false) {
    policy(policy_value);
    enter_debug(child);
    const unsigned select = child.privilege == PRV_U ? CSR_UISELECT : CSR_SISELECT;
    const unsigned alias = child.privilege == PRV_U ? CSR_UIREG : CSR_SIREG;
    const unsigned selection = child.privilege == PRV_U ? CSR_UIREG5 : CSR_SIREG5;
    const reg_t enable = child.privilege == PRV_U ? CSR_MCONTROL6_U : CSR_MCONTROL6_S;
    write(select, SISELECT_TRIG);
    for (unsigned index = 0; index < 2; ++index) {
      write(selection, index);
      write(alias, disabled);
      write(alias + 1, victim + index * 0x100);
      write(alias + 2, 0);
      write(alias, type6 | CSR_MCONTROL6_DMODE(64) | enable | CSR_MCONTROL6_EXECUTE |
            (self_hosted ? 0 : reg_t(1) << CSR_MCONTROL6_ACTION_OFFSET));
      check("debugger installed DMODE trigger", (read(alias) & CSR_MCONTROL6_DMODE(64)) != 0, 1);
    }
    write(selection, 1);
    write(CSR_UISELECT, 0x321);
    leave_debug(child);
  }
  void execute_victim(mode child, reg_t pc = victim) {
    context(child);
    p.get_state()->pc = pc;
    p.get_mmu()->flush_icache();
    p.step(1);
  }
};

struct bank {
  fixture& f;
  mode manager;
  unsigned alias, selection, selector;
  bank(fixture& f_, mode m) : f(f_), manager(m),
      alias(m.privilege == PRV_M ? CSR_TDATA1 : CSR_SIREG),
      selection(m.privilege == PRV_M ? CSR_TSELECT : CSR_SIREG5),
      selector(m.privilege == PRV_M ? 0 : CSR_SISELECT) {
    f.context(manager);
    if (selector) f.write(selector, SISELECT_TRIG);
  }
  void choose(unsigned index) { f.write(selection, index); }
  reg_t read(unsigned field) { return f.read(alias + field); }
  void write(unsigned field, reg_t value) { f.write(alias + field, value); }
};

struct snapshot {
  std::array<std::array<reg_t, 3>, 2> triggers;
  reg_t selection, user_selector;
};

snapshot save(bank& b) {
  snapshot s;
  s.selection = b.f.read(b.selection);
  s.user_selector = b.f.read(CSR_UISELECT);
  for (unsigned index = 0; index < 2; ++index) {
    b.choose(index);
    for (unsigned field = 0; field < 3; ++field) s.triggers[index][field] = b.read(field);
  }
  return s;
}

void clear(bank& b) {
  for (unsigned index = 0; index < 2; ++index) {
    b.choose(index);
    b.write(0, disabled);
    b.write(1, 0);
    b.write(2, 0);
  }
  b.f.write(CSR_UISELECT, 0);
}

void restore(bank& b, const snapshot& s) {
  clear(b);
  for (unsigned index = 0; index < 2; ++index) {
    b.choose(index);
    b.write(1, s.triggers[index][1]);
    b.write(2, s.triggers[index][2]);
    b.write(0, s.triggers[index][0]);
  }
  b.f.write(b.selection, s.selection);
  b.f.write(CSR_UISELECT, s.user_selector);
}

void check_clean(bank& b, const std::string& label) {
  for (unsigned index = 0; index < 2; ++index) {
    b.choose(index);
    check(label + " disabled type", b.read(0), disabled);
    check(label + " cleared address", b.read(1), 0);
    check(label + " cleared context qualifier", b.read(2), 0);
  }
}

void lifecycle(const std::string& name, mode manager, mode child, reg_t allowed_policy,
               bool pending_icount = false) {
  std::cout << "SCENARIO " << name << "\n";
  fixture f;
  f.arm(child, allowed_policy);
  if (pending_icount) {
    f.enter_debug(child);
    const unsigned alias = child.privilege == PRV_U ? CSR_UIREG : CSR_SIREG;
    const unsigned select = child.privilege == PRV_U ? CSR_UIREG5 : CSR_SIREG5;
    const reg_t enable = child.privilege == PRV_U ? CSR_ICOUNT_U : CSR_ICOUNT_S;
    f.write(CSR_UISELECT, SISELECT_TRIG);
    f.write(select, 0);
    f.write(alias, disabled);
    f.write(alias, (reg_t(3) << 60) | CSR_ICOUNT_DMODE(64) | enable |
            CSR_ICOUNT_PENDING | (reg_t(2) << CSR_ICOUNT_COUNT_OFFSET) | 1);
    check(name + " pending icount installed", f.read(alias) & CSR_ICOUNT_PENDING, CSR_ICOUNT_PENDING);
    f.write(select, 1);
    f.write(CSR_UISELECT, 0x321);
    f.leave_debug(child);
  }
  bank b(f, manager);
  auto original = save(b);
  check(name + " manager sees DMODE", (original.triggers[0][0] & CSR_MCONTROL6_DMODE(64)) != 0, 1);
  clear(b);
  check_clean(b, name);
  f.policy(0);
  f.execute_victim(child);
  check(name + " protected context remains outside Debug Mode", f.p.get_state()->debug_mode, 0);
  check(name + " protected instruction retires without a trap", f.p.get_state()->pc, victim + 4);
  check(name + " protected context receives clean user selector", f.read(CSR_UISELECT), 0);
  f.context(manager);
  bank resumed(f, manager);
  restore(resumed, original);
  check(name + " restored selection", f.read(resumed.selection), original.selection);
  check(name + " restored user selector", f.read(CSR_UISELECT), original.user_selector);
  auto actual = save(resumed);
  for (unsigned index = 0; index < 2; ++index)
    for (unsigned field = 0; field < 3; ++field)
      check(name + " exact trigger restore", actual.triggers[index][field], original.triggers[index][field]);
  f.policy(allowed_policy);
  f.execute_victim(child);
  check(name + " restored debugger trigger fires", f.p.get_state()->debug_mode, 1);
  check(name + " restored breakpoint cause", f.p.get_state()->dcsr->cause, CSR_DCSR_CAUSE_TRIGGER);
  check(name + " restored breakpoint PC", f.p.get_state()->dpc->read(), victim);
}

void mixed_u_vu_management(bool physical_u_debug) {
  std::cout << "SCENARIO VS manages VU with physical U debug " << physical_u_debug << '\n';
  fixture f;
  f.arm(vu, 8 | (physical_u_debug ? 4 : 0), true);
  f.policy(physical_u_debug ? 4 : 0);
  check("VU debug revoked before entering protected application", f.p.is_debug_allowed(PRV_U, true), 0);
  check("VS manager itself is not externally debuggable", f.p.is_debug_allowed(PRV_S, true), 0);
  check("physical U permission is independent of protected VU", f.p.is_debug_allowed(PRV_U, false), physical_u_debug);
  f.context(vs);
  bank guest(f, vs);
  const reg_t visible = guest.read(0);
  clear(guest);
  // Trusted HS observation tests whether VS's actual CSR writes took effect.
  f.context(hs);
  bank host(f, hs);
  host.choose(0);
  const reg_t after = host.read(0);
  check("VS reads VU DMODE state independently of physical U permission", (visible & CSR_MCONTROL6_DMODE(64)) != 0, 1);
  check("VS clears VU trigger without HS assistance", after, disabled);
  f.execute_victim(vu);
  check("sanitized protected VU instruction retires", f.p.get_state()->pc, victim + 4);
  check("sanitized protected VU stays outside Debug Mode", f.p.get_state()->debug_mode, 0);
}

void mixed_policy_dmode_zero_control() {
  std::cout << "SCENARIO control: VS can manage DMODE=0 with physical U debug enabled\n";
  fixture f;
  f.arm(vu, 12, true);
  f.enter_debug(vu);
  f.write(CSR_UISELECT, SISELECT_TRIG);
  for (unsigned index = 0; index < 2; ++index) {
    f.write(CSR_UIREG5, index);
    f.write(CSR_UIREG, f.read(CSR_UIREG) & ~CSR_MCONTROL6_DMODE(64));
    check("DMODE=0 positive control installed", f.read(CSR_UIREG) & CSR_MCONTROL6_DMODE(64), 0);
  }
  f.leave_debug(vu);
  f.policy(4);
  bank b(f, vs);
  auto s = save(b);
  check("VS can save ordinary self-hosted VU trigger under mixed policy", s.triggers[0][1], victim);
  clear(b);
  check_clean(b, "VS mixed-policy DMODE=0 control");
  f.execute_victim(vu);
  check("VS-cleared ordinary trigger does not affect protected VU", f.p.get_state()->pc, victim + 4);
}

void revocation_without_sanitization() {
  std::cout << "SCENARIO negative control: revocation alone is not sanitization\n";
  fixture f;
  f.arm(user, 4, true);
  f.policy(0);
  f.context(hs);
  f.write(CSR_SSTATEEN0, ~SSTATEEN0_TR);
  f.execute_victim(user);
  check("revoking CSR access does not disable an existing self-hosted trigger", f.p.get_state()->mcause->read(), CAUSE_BREAKPOINT);
  check("unsanitized breakpoint reveals the matched instruction address", f.p.get_state()->mepc->read(), victim);
  check("revocation negative control does not enter Debug Mode", f.p.get_state()->debug_mode, 0);
  f.context(hs);
  f.write(CSR_SSTATEEN0, ~reg_t(0));
  bank b(f, hs);
  clear(b);
  f.execute_victim(user);
  check("positive control: clearing the bank removes inherited execution influence", f.p.get_state()->pc, victim + 4);
}

bool unsanitized_guest_observation(bool protected_match) {
  std::cout << "SCENARIO negative control: omitted VS cleanup, protected match="
            << protected_match << '\n';
  fixture f;
  f.arm(vu, 12, true);
  f.policy(4);
  // Deliberately omit the available VS cleanup and the mandatory clean bank.
  // This demonstrates the consequence; it is not a spec-compliant handoff.
  f.execute_victim(vu, victim + (protected_match ? 0 : 4));
  check("negative control: protected VU is never externally halted", f.p.get_state()->debug_mode, 0);
  f.policy(12);
  f.enter_debug(vu);
  f.write(CSR_UISELECT, SISELECT_TRIG);
  f.write(CSR_UIREG5, 0);
  const reg_t hit = f.read(CSR_UIREG) & (CSR_MCONTROL6_HIT0 | CSR_MCONTROL6_HIT1);
  check("negative control: resumed VU debugger observes protected path through hit", hit != 0, protected_match);
  f.leave_debug(vu);
  return hit != 0;
}

void protected_action_one() {
  std::cout << "SCENARIO protected execution does not update ACTION=1 hit state\n";
  fixture f;
  f.arm(user, 4);
  f.policy(0);
  f.execute_victim(user);
  check("denied ACTION=1 does not enter Debug Mode", f.p.get_state()->debug_mode, 0);
  check("denied ACTION=1 permits the protected instruction", f.p.get_state()->pc, victim + 4);
  f.context(hs);
  bank b(f, hs);
  b.choose(0);
  check("denied ACTION=1 does not record a protected hit", b.read(0) & (CSR_MCONTROL6_HIT0 | CSR_MCONTROL6_HIT1), 0);

  f.policy(4);
  f.enter_debug(user);
  f.write(CSR_UISELECT, SISELECT_TRIG);
  f.write(CSR_UIREG5, 0);
  f.write(CSR_UIREG, disabled);
  f.write(CSR_UIREG, (reg_t(3) << 60) | CSR_ICOUNT_DMODE(64) | CSR_ICOUNT_U |
          CSR_ICOUNT_PENDING | (reg_t(2) << CSR_ICOUNT_COUNT_OFFSET) | 1);
  f.leave_debug(user);
  f.policy(0);
  f.execute_victim(user);
  check("denied pending icount does not enter Debug Mode", f.p.get_state()->debug_mode, 0);
  check("denied pending icount permits the protected instruction", f.p.get_state()->pc, victim + 4);
  bank counter(f, hs);
  counter.choose(0);
  const reg_t protected_count = counter.read(0);
  check("denied icount does not count protected instructions", protected_count & CSR_ICOUNT_COUNT,
        reg_t(2) << CSR_ICOUNT_COUNT_OFFSET);
  check("denied icount does not consume its pending event", protected_count & CSR_ICOUNT_PENDING, CSR_ICOUNT_PENDING);
  check("denied icount does not record a protected hit", protected_count & CSR_ICOUNT_HIT, 0);
  f.policy(4);
  f.execute_victim(user);
  check("same-principal positive control: pending icount fires when permission returns", f.p.get_state()->debug_mode, 1);
  check("pending icount resumes only at the allowed context's PC", f.p.get_state()->dpc->read(), victim);
}

void uniform_policy_contexts() {
  std::cout << "SCENARIO negative control: uniform policy is not per-domain trigger banking\n";
  fixture f;
  f.arm(user, 4);
  bank manager(f, hs);
  auto a = save(manager);
  // Context B has the same external-debug policy. Without a software swap it
  // sees A's state. This intentionally omits the spec's shared-state handling.
  f.enter_debug(user);
  f.write(CSR_UISELECT, SISELECT_TRIG);
  f.write(CSR_UIREG5, 0);
  check("unswapped equal-policy domain B observes A's trigger address", f.read(CSR_UIREG2), victim);
  f.leave_debug(user);
  bank clean(f, hs);
  clear(clean);
  f.enter_debug(user);
  f.write(CSR_UISELECT, SISELECT_TRIG);
  f.write(CSR_UIREG5, 0);
  check("clean equal-policy domain B sees a disabled trigger", f.read(CSR_UIREG), disabled);
  check("clean equal-policy domain B sees no A address", f.read(CSR_UIREG2), 0);
  f.leave_debug(user);
  bank back(f, hs);
  restore(back, a);
  f.enter_debug(user);
  f.write(CSR_UISELECT, SISELECT_TRIG);
  f.write(CSR_UIREG5, 0);
  check("returning domain A recovers its own trigger address", f.read(CSR_UIREG2), victim);
  f.leave_debug(user);
}

void physical_guest_selector_switch() {
  std::cout << "SCENARIO HS swaps physical U and VU shared user state\n";
  fixture f;
  f.arm(user, 4);
  bank b(f, hs);
  auto physical = save(b);
  clear(b);
  f.arm(vu, 8);
  bank guest_bank(f, hs);
  // VU uses a distinct selector value and selected trigger index.
  f.write(CSR_UISELECT, 0x456);
  f.write(CSR_SIREG5, 0);
  auto guest = save(guest_bank);
  restore(guest_bank, physical);
  f.policy(4);
  f.context(user);
  check("physical U selector survives guest execution", f.read(CSR_UISELECT), 0x321);
  bank physical_bank(f, hs);
  auto actual_physical = save(physical_bank);
  for (unsigned index = 0; index < 2; ++index)
    check("physical U mode enables restored without VU enables", actual_physical.triggers[index][0], physical.triggers[index][0]);
  restore(physical_bank, guest);
  f.policy(8);
  f.context(vu);
  check("guest VU selector restored separately", f.read(CSR_UISELECT), 0x456);
  bank restored_guest(f, hs);
  auto actual_guest = save(restored_guest);
  check("guest trigger selection restored separately", actual_guest.selection, guest.selection);
  for (unsigned index = 0; index < 2; ++index)
    check("guest VU mode enables restored without physical U enables", actual_guest.triggers[index][0], guest.triggers[index][0]);
}

void u_vs_boundary(reg_t policy, bool swap_context) {
  std::cout << "SCENARIO U/VS boundary policy=" << policy
            << " HS_swap=" << swap_context << '\n';
  fixture f;
  if (policy & 4) {
    f.arm(user, policy, true);
  } else {
    f.policy(policy);
    f.context(user);
    f.write(CSR_UISELECT, SISELECT_TRIG);
    for (unsigned index = 0; index < 2; ++index) {
      f.write(CSR_UIREG5, index);
      f.write(CSR_UIREG, type6 | CSR_MCONTROL6_U | CSR_MCONTROL6_EXECUTE);
      f.write(CSR_UIREG2, victim + index * 0x100);
    }
    f.write(CSR_UISELECT, 0x321);
  }

  bank host(f, hs);
  const auto physical = save(host);
  for (unsigned index = 0; index < 2; ++index) {
    check("physical U trigger address seeded", physical.triggers[index][1], victim + index * 0x100);
    check("physical U trigger has only its native user mode enabled",
          physical.triggers[index][0] & (CSR_MCONTROL6_U | CSR_MCONTROL6_VU), CSR_MCONTROL6_U);
    check("physical U trigger DMODE matches its owner",
          (physical.triggers[index][0] & CSR_MCONTROL6_DMODE(64)) != 0, (policy & 4) != 0);
  }
  if (swap_context) clear(host);

  // With VS debug enabled, the VS debugger exercises delegated access. With
  // VS debug disabled, VS software itself manages the delegated trigger bank.
  const bool guest_debugger = (policy & 2) != 0;
  if (guest_debugger) f.enter_debug(vs);
  else f.context(vs);
  f.write(CSR_SISELECT, SISELECT_TRIG);
  f.write(CSR_SIREG5, 0);
  check("VS receives its own trigger address, not physical U state", f.read(CSR_SIREG2),
        swap_context ? 0 : victim);
  if (policy == 12 && !swap_context)
    check("negative control: VS can access unswapped physical U DMODE=1", f.read(CSR_SIREG) & CSR_MCONTROL6_DMODE(64), CSR_MCONTROL6_DMODE(64));
  for (unsigned index = 0; index < 2; ++index) {
    f.write(CSR_SIREG5, index);
    f.write(CSR_SIREG, disabled);
    f.write(CSR_SIREG2, base + 0x6000 + index * 0x100);
    f.write(CSR_SIREG3, 0);
    f.write(CSR_SIREG, type6 | CSR_MCONTROL6_U | CSR_MCONTROL6_EXECUTE);
  }
  f.write(CSR_SIREG5, 0);
  f.write(CSR_UISELECT, 0x456);
  if (guest_debugger) f.leave_debug(vs);

  bank returning(f, hs);
  const auto guest = save(returning);
  for (unsigned index = 0; index < 2; ++index) {
    check("guest trigger address seeded", guest.triggers[index][1], base + 0x6000 + index * 0x100);
    check("guest trigger has only its native virtual-user mode enabled",
          guest.triggers[index][0] & (CSR_MCONTROL6_U | CSR_MCONTROL6_VU), CSR_MCONTROL6_VU);
  }
  if (swap_context) restore(returning, physical);
  const auto actual = save(returning);
  for (unsigned index = 0; index < 2; ++index) {
    for (unsigned field = 0; field < 3; ++field)
      check("return to U preserves its trigger context only with HS swap",
            actual.triggers[index][field],
            swap_context ? physical.triggers[index][field] : guest.triggers[index][field]);
    if (!swap_context)
      check("negative control: guest changed physical U trigger address",
            actual.triggers[index][1] != physical.triggers[index][1], 1);
  }
  f.context(user);
  check("U receives its saved user selector", f.read(CSR_UISELECT),
        swap_context ? physical.user_selector : guest.user_selector);
  if (policy & 4) {
    f.enter_debug(user);
    f.write(CSR_UISELECT, SISELECT_TRIG);
    f.write(CSR_UIREG5, 0);
    check("U debugger observes its own restored address", f.read(CSR_UIREG2),
          swap_context ? victim : base + 0x6000);
    f.leave_debug(user);
  }

  bank guest_return(f, hs);
  restore(guest_return, guest);
  const auto restored_guest = save(guest_return);
  for (unsigned index = 0; index < 2; ++index)
    for (unsigned field = 0; field < 3; ++field)
      check("return to VS restores the guest trigger context",
            restored_guest.triggers[index][field], guest.triggers[index][field]);
  check("VS user selector restored independently", f.read(CSR_UISELECT), guest.user_selector);
  f.context(machine);
  check("U/VS boundary preserves the unchanged debug policy", f.read(CSR_MDTCFG), policy);
}

void clean_handoff_removes_hidden_fields() {
  std::cout << "SCENARIO clean delegation removes hidden native qualifiers\n";
  fixture f;
  f.context(machine);
  f.write(CSR_TSELECT, 0);
  f.write(CSR_TDATA1, type6 | CSR_MCONTROL6_M | CSR_MCONTROL6_S | CSR_MCONTROL6_U);
  const reg_t qualifier = (reg_t(1) << CSR_TEXTRA64_MHVALUE_OFFSET) |
                         (reg_t(4) << CSR_TEXTRA64_MHSELECT_OFFSET);
  f.write(CSR_TDATA3, qualifier);
  require(f.read(CSR_TDATA3) != 0, "native qualifier positive control is zero");
  f.context(vs);
  f.write(CSR_SISELECT, SISELECT_TRIG);
  f.write(CSR_SIREG5, 0);
  check("delegated view hides machine qualifier without clearing it", f.read(CSR_SIREG3), 0);
  f.context(machine);
  check("hidden native qualifier persists until explicit sanitization", f.read(CSR_TDATA3), qualifier);
  bank b(f, machine);
  clear(b);
  f.context(vu);
  f.write(CSR_UISELECT, SISELECT_TRIG);
  f.write(CSR_UIREG5, 0);
  f.write(CSR_UIREG, type6 | CSR_MCONTROL6_U | CSR_MCONTROL6_EXECUTE);
  f.write(CSR_UIREG2, victim);
  f.execute_victim(vu);
  check("clean delegated self-hosted trigger executes", f.p.get_state()->mcause->read(), CAUSE_BREAKPOINT);
  check("clean delegated trigger has no inherited machine qualifier", f.p.get_state()->mepc->read(), victim);
}
} // namespace

int main() {
  try {
    setenv("RISCV_MDBGEN_INIT", "0", 1);
    setenv("RISCV_MDTCFG_INIT", "0", 1);
    lifecycle("M manages HS", machine, hs, 1);
    lifecycle("HS manages U", hs, user, 4);
    lifecycle("HS manages VS", hs, vs, 2);
    lifecycle("VS manages VU", vs, vu, 8);
    lifecycle("HS saves pending user icount", hs, user, 4, true);
    lifecycle("VS saves pending VU icount", vs, vu, 8, true);
    mixed_u_vu_management(false);
    mixed_u_vu_management(true);
    mixed_policy_dmode_zero_control();
    check("negative control: protected paths are distinguishable without successful sanitization",
          unsanitized_guest_observation(false) != unsanitized_guest_observation(true), 1);
    revocation_without_sanitization();
    protected_action_one();
    uniform_policy_contexts();
    physical_guest_selector_switch();
    for (reg_t policy : {reg_t(2), reg_t(4), reg_t(6), reg_t(8), reg_t(10), reg_t(12), reg_t(14)})
      u_vs_boundary(policy, true);
    u_vs_boundary(12, false);
    clean_handoff_removes_hidden_fields();
    std::cout << "SUMMARY checks=" << checks << " conformance_failures=" << failures << '\n';
    return failures ? 1 : 0;
  } catch (const std::exception& e) {
    std::cerr << "HARNESS ERROR " << e.what() << '\n';
    return 2;
  }
}
