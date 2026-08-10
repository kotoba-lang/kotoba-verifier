# kotoba-verifier

Independent artifact verifier — re-derives emission from KIR and rejects drift.

**Tier**: `T2`  **Role**: `verifier`

Split out of the overloaded core repos by ADR-2607266000 so that each
responsibility has exactly one owner and the dependency direction is
checkable from outside.

## Owns

- `kotoba.verifier (target contract + re-emission equality check)`

For native record scalar replacement, the verifier independently admits only
one `if` with two direct constructors of the same non-empty fixed
`:i64`/`:bool` record, either projected directly or named by one `let`. It
continues to reject schema drift, symbol forwarding, nested/non-scalar
aggregates, and escaping aggregate ABI claims.

For native variant scalar replacement, the verifier independently admits a
sealed variant only when every payload is `:i64` or `:bool` and the value is a
direct constructor, one local binding, or one same-schema variant-valued `if`.
Matches must cover every case in declaration order. Legacy directly nested
matches retain their established wider payload support; local symbol
forwarding and variant parameters/results remain rejected.

The verifier pins the native producer containing aggregate-boundary contract
v2. It checks that the existing record boundary is still a one-word,
context-owned pair-chain handle, record and variant crossings remain `:held`,
and scalar direct calls are admitted only with the complete per-function
frame/clobber guarantee set. It also re-emits a two-function call module with
the pinned production emitter and checks that its representative caller uses
the liveness-minimal `:call-live` policy with one slot, save, and reload.
Reading this producer contract does not widen
the verifier's independently derived record or variant predicates.

## Does not own

- produce artifacts
- be a dependency of the producer it verifies

## Depends on

- `kotoba-lang/kotoba-kir`
- `kotoba-lang/artifact`
- `kotoba-lang/kotoba-wasm`
- `kotoba-lang/kotoba-native`

## Test

```bash
clojure -M:test
```
