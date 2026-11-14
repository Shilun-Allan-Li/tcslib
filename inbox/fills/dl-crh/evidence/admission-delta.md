# Exact admission delta

Status: **PASS**.

Verified 176 completed successful modules from `evidence/logs/final-sweep-verified/results.jsonl`; raw log hashes
and the checked source hashes match. For retries, only each module's latest record is used.

Baseline: 22 admitted declarations. Final: 21.
Required delta: remove only `TCSlib/Cryptography/Hashing/FromDiscreteLog.dlHash_crh`.

## Removed

- `TCSlib/Cryptography/Hashing/FromDiscreteLog`: `dlHash_crh` (count 1).

## Added

None.

The JSON companion retains every raw warning, its log/source location, and the full final list.
