# 0052 — re-emit with the recorded emitter

Status: accepted
Date: 2026-10-03
Related: amu ADR 0365 (opt-in `--backend seed`), amu docs/selfhost-seed-merge-20261003.md section 00

## Context

`verify-artifact!` re-emits an artifact's `:program` with this file's own
emitter (`target-contracts`, `kotoba.native.aarch64/emit-program` for AArch64)
and compares `:code` and `:exports` byte for byte. amu now has a second AArch64
emitter: the selfhost seed's backend (`seed compile-kir`), opt-in, which emits
different bytes for the same KIR (it was shown to BEHAVE the same on 357 exports,
not to emit the same instructions). An artifact whose code the seed emitted
cannot pass a check that re-emits with machine_ir, and it must not be admitted
by skipping the check.

## Decision

- An artifact may carry ONE more field, `:emitter`, present only when another
  emitter produced its code: `{:name :kotoba-seed :sha256 <64 hex> :route
  :bootstrap-process}`, closed (exactly those keys and values; anything else is
  "native artifact emitter record rejected"). It is under the artifact seal.
- The re-emission uses the RECORDED emitter. This file cannot run it (the seed
  is a separate program reached through the host's process ability), so the
  caller supplies it through the dynamic var `*emitters*`: sha256 -> function
  KIR program -> `{:code :exports}`. The caller binds a sha256 only to a
  function that runs the program with those bytes (amu hashes the seed command
  and runs a private copy written from the hashed bytes).
- A record with no binding is refused by name: "recorded emitter is not
  available to this verifier". It is never re-emitted by the built-in emitter
  and never skipped. A record on a non-AArch64 target is refused ("recorded
  emitter does not serve this target").
- Everything else is unchanged: lowering mode, fuel ABI, limits, context ABI,
  KIR checks, the oracle, and the byte comparison itself. An artifact without
  `:emitter` verifies exactly as before (`*emitters*` defaults to `{}`).

## Consequences

Tested on nbb by test/kotoba/verifier_emitter_test.cljk (6 tests, 11
assertions): unbound record refused by name; a binding for another sha256
refused; a binding that emits the same bytes admits; a binding that changes one
byte is refused as the instruction stream; malformed records refused; editing
the record after sealing breaks the seal. amu's lock pin (a560612e) predates
this; amu falls back to machine_ir when the loaded verifier has no `*emitters*`.
