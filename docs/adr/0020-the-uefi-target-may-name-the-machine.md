# ADR-0020: The UEFI firmware target may name the machine

- Status: accepted
- Date: 2026-09-02

## Context

`verify-runtime!` admitted the kernel-facing operations -- port I/O, control
registers, the interrupt-flag instructions, the bounded memory family -- for
`:x86_64-aiueos-kernel-v1` and `:aarch64-aiueos-kernel-v1` and refused every
other target with "bounded kernel memory operation requires the aiueos kernel
target".

`:x86_64-aiueos-uefi-v1` was one of the refused. That is the target whose own
profile says `:execution :firmware`, `:runtime :none`,
`:ambient-syscalls false` -- a UEFI application runs at CPL0 on an
identity-mapped machine with boot services live, which is the same execution
surface the kernel targets name, reached earlier. Refusing it a port write
refused the target its own profile describes, and it is a large part of why
aiueos's BOOTX64.EFI is still C: a bootloader cannot say anything at all
without one.

## Decision

`:x86_64-aiueos-uefi-v1` joins the admitted set. The four UEFI firmware
operations (`kernel-system-table`, `kernel-load-ptr`, `kernel-uefi-call2`,
`kernel-jump-to`, kotoba-gmir ADR-0008) join the operation list, so an
ordinary native target is refused here as well as by amu's own target gate --
two refusals, because a gate on one route is not a gate.

## Consequences

- This repository pins kotoba-native itself, deliberately, and that pin
  predates the four operations' encodings. The new tests therefore assert
  admission with `kernel-out-u8`/`kernel-in-u8`, which this pin can emit.
  They deliberately do NOT assert the four operations' refusal on an ordinary
  target: measured at this pin, `(kernel-load-ptr 4096 64)` on
  `:x86_64-kotoba-v1` throws "aggregate ABI rejected: call-abi-not-admitted",
  because a backend that predates the operation reads it as a call to an
  unknown function -- a refusal that would still happen with the target rule
  deleted. Four green assertions that discriminate nothing are worse than
  none. Their gate is tested in amu, where the toolchain is new enough.
- The rule now separates FIRMWARE from ordinary native, not KERNEL from
  everything. A future ring-3 aiueos target would still be refused, which is
  correct: `:x86_64-aiueos-user-v1` is `:execution :process`.
- Break-checked: removing `:x86_64-aiueos-uefi-v1` from the set turns the two
  admission cases red with exactly this ADR's message.
