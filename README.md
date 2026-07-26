# kotoba-verifier

Independent artifact verifier — re-derives emission from KIR and rejects drift.

**Tier**: `T2`  **Role**: `verifier`

Split out of the overloaded core repos by ADR-2607266000 so that each
responsibility has exactly one owner and the dependency direction is
checkable from outside.

## Owns

- `kotoba.verifier (target contract + re-emission equality check)`

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
