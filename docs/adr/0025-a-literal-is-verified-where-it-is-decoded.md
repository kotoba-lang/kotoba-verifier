# ADR-0025: A literal is verified where it is decoded, and the pin that would have proved it costs 22 tests

- Status: accepted
- Date: 2026-09-02

## Context

kotoba-gmir ADR-0011 added `:gmir/rodata-address` and two wider firmware calls.
This verifier re-derives every operation's arity independently of the frontend,
so both need rows; and a literal has something an arity does not cover, which
is whether its CONTENT decodes.

## Decision

**`kernel-uefi-call4` (6) and `kernel-uefi-call6` (8) join the privileged arity
table, the kernel-native set and the aiueos-target set.** A five-operand
`kernel-uefi-call4` would pass whatever the register happened to hold as the
fourth UEFI argument, and `AllocatePages` writes through its fourth.

**`ucs2`, `guid`, `bytes-literal` and `bytes-literal-length` are verified for
arity, for the argument being a string, and for the CONTENT.** The content
check is the one worth arguing: a malformed GUID has no failure mode
downstream. Sixteen bytes get placed either way and the firmware answers
`EFI_UNSUPPORTED`, which is exactly what a machine WITHOUT that protocol
answers.

The decoder is `kotoba.gmir/rodata-bytes`, reached through a **top-level**
`kotoba-gmir` dependency rather than through `kotoba-native`. That is a
measurement, not a preference: bumping the `kotoba-native` pin far enough to
carry the newer gmir imports **22 failures** in `pinned-producer-*`, which pin
allocator output shapes across an allocator change this stream does not own.
Measured 2026-09-02 -- main is 67 tests / 425 assertions / 0 failures, and the
same suite at `kotoba-native fdd580e` is 67 / 429 / 30. A top-level git
dependency wins over a transitive one, so this reaches the decoder without
moving the backend.

**The literal address heads join `kernel-native-operations`; the LENGTH head
does not.** That set has to agree with `kotoba.kir/lower`'s own, and when the
two disagree the failure surfaces in neither one's terms -- the compiler seals
no value, this side re-executes the entry, gets the oracle's refusal, and
reports an oracle mismatch it never had. kotoba-kir answers
`bytes-literal-length` rather than trapping, because the answer is a property
of the literal TEXT, so it is left out here too.

## Consequences

- The refusals are asserted by calling `verify-program!` directly. Two other
  routes were tried and both went red for the wrong reason, and the helper's
  docstring says so: `privileged-artifact` calls the BACKEND to build `:code`,
  so a malformed body is refused as `machine IR rejected:
  rodata-literal-malformed` before the verifier sees it -- green with every
  line of this check deleted -- and substituting a body into an already-built
  artifact fails at `artifact integrity mismatch`, because the seal covers the
  program.
- The literal TARGET rule is asserted in amu, where the toolchain is pinned new
  enough to emit a literal, for the reason
  `an-ordinary-native-target-still-may-not` already records for the four
  ADR-0020 operations.
