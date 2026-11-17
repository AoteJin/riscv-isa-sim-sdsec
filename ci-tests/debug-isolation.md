# External debug isolation audit

This audit tests the software isolation procedures in the external debug security
specification, including the November 17, 2026 updates to VS DMODE access and
S/HS trigger context switching at U-mode/VS-mode boundaries.

Run it after building Spike:

```sh
ci-tests/test-debug-isolation build
# Equivalent build target:
make -C build check-debug-isolation
```

The program exits with 0 when the checks pass, 1 when a check fails, and 2 for a
harness failure. `make` reports its
own nonzero exit status when the program fails. This is a separate audit target;
the existing `make check` regression target retains its existing checks.

The current result is **494 checks and zero failures** across 24 scenarios. The
audit program exits with 0. No architectural security violation is established.

## Shared trigger management under independent U/VU policy

The specification defines this combination:

| Control | Allowed VU application A | Protected VU application B |
| --- | --- | --- |
| `mdbgen` | 0 | 0 |
| `SEDBGEN` | 0 | 0 |
| `VSEDBGEN` | 0 | 0 |
| `UEDBGEN` | 1 | 1 |
| `VUEDBGEN` | 1 | 0 |

All applicable TR, CSRIND, and UCSRIND gates are enabled. Application A's debugger
programs `DMODE=1` triggers through the VU interface.

The DMODE rules in `smtdeleg.adoc` and `sutcfg.adoc` allow VS to read and write
these triggers outside Debug Mode when `mdbgen=0`, `SEDBGEN=0`, and `VSEDBGEN=0`.
`UEDBGEN` and `VUEDBGEN` do not restrict that access. Actual VS CSR instructions
save and clear A's `DMODE=1` trigger state before B runs, without HS assistance.

The controls verify:

* VS manages `DMODE=1` VU state with either value of `UEDBGEN`.
* VS manages `DMODE=0` VU state with `UEDBGEN=1`.
* Successful VS cleanup removes trigger influence from the protected VU context.

The negative controls deliberately launch B without performing VS cleanup.
A retained `ACTION=0` trigger then records whether B executes its match address.
When A's VU debug permission returns, A's debugger reads different hit values for
the two protected paths. B never enters Debug Mode. These negative controls do
**not** satisfy the required clean-state handoff; they demonstrate the consequence
of omitting that cleanup.

## S/HS context switching at U-mode/VS-mode boundaries

S/HS saves the outgoing trigger context and restores the incoming trigger context
at a U-mode/VS-mode boundary when any of `UEDBGEN`, `VSEDBGEN`, or `VUEDBGEN` is set
in either context. The requirement applies with an unchanged debug policy.

The audit exercises all seven nonzero combinations of those three enables. U
owns a trigger bank, VS software or a VS debugger programs its guest bank, and
S/HS restores the appropriate bank on each return. U's addresses and native mode
enables remain unchanged, and the guest recovers its own trigger state.

A negative control omits the S/HS swap with `UEDBGEN=1` and `VUEDBGEN=1`. VS then
reads and changes the unswapped U trigger state, and the returning U debugger
observes the changed address. This control violates the required boundary switch
and is not counted as an architectural bypass.

## Other tested procedures

| IDs | Procedure | Observation |
| --- | --- | --- |
| T88 | M→HS, HS→U, HS→VS, VS→VU trigger context switching | Two trigger slots, selection, and user indirect selection save and restore exactly; the protected context runs with a clean bank; the restored breakpoint fires at the original PC. |
| T89 | Pending `icount` context | Pending and count state are cleared for the protected context and restored for the original context. |
| T90 | Independent U/VU policies | VS directly saves and clears VU `DMODE=1` state independently of physical U debug permission. |
| T91 | Revocation without cleanup | Clearing TR and debug permission does not erase a preexisting self-hosted trigger. Explicit cleanup removes its execution influence. This is a negative control. |
| T92 | Denied `ACTION=1` execution | Neither address-trigger hit state nor instruction-count state records protected execution; pending events remain pending until permission returns. |
| T93 | Physical U / VU shared state | HS swaps the shared user selector, trigger selection, and native U/VU mode enables independently. |
| T94 | Clean-state preparation | Read-only-zero aliases hide native qualifiers without erasing them. Trusted cleanup removes them before delegation. |
| T95 | Uniform-policy contexts | Omitting a state swap exposes the previous context's trigger configuration. A clean bank and explicit restore isolate it. This is a negative control, not an architectural finding. |
| T96 | U-mode/VS-mode boundaries | S/HS swaps both trigger slots and selectors under all seven nonzero lower-privilege debug-enable combinations. The unswapped U+VU case reproduces trigger corruption as a negative control. |

## Scope

CSR reads and writes and victim instructions execute in Spike. Trusted setup uses
the processor API, and a harness scheduler establishes privilege/context
boundaries. The fixture represents an untrusted external debugger with Debug Mode
entry and CSR instructions at the derived debug access privilege. It does not use
OpenOCD redirection or fabricated CSR errors.

The audit uses RV64 with H and bare address translation. It does not execute an OS
scheduler, SBI implementation, DMI transport, authorization-handoff platform
controller, protected system bus, or RTL. The two secret-path negative controls
observe trigger hit state through the resumed VU debugger's CSR access; observing
an M-mode trap CSR is not their leak oracle.

No unsafe implementation behavior in a scenario where the specification leaves
behavior undefined is classified as an architectural security bypass. In
particular, this audit does not revoke `mdbgen` while the hart is in Debug Mode.
