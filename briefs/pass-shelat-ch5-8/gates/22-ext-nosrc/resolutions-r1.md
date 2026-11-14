# Gate 22 · resolutions, round 1 · CLOSED

Codex's verdict is **CLEAR**, with 0 blockers, 0 majors, 0 minors and 0 notes. No new finding was raised.

- **Findings:** `findings/gate22-ext-nosrc-findings.md`, SHA-256 `abb3d05d9dd634ed7a77472a2cd0e4085d03ef9ad8997701a0f9d8f3b36efeab`.
- **Audited head:** `e99a6055ff6b24cdf4b25993e83d045bd569028f`, tree `962374efbcb153c8f696b96f74aae0cab4a2baff`.
- **Pins:** records `1d109ff037d12cc6520ba0fb7826e320da348d73`, exchange `7e84141907941e0d684942f370f9830eaeb555e5`.
- **Live check:** the PR branch `land/pass-shelat-ext-nosrc` is still at the audited head.

## What the auditor checked
The auditor did not run Lean. Its own checks covered:
- **Integrity:** the gate `SHA256SUMS` (15/15), `verification.zip` (42/42) and the nested review and LE-doc archives (352/352 and 53/53); the original delivery (846/846 and 837/837); the patch replay; the PR diff (4 paths, +949/−6); and the 203-file source closure.
- **Proof:** a full mathematical re-check of Theorem 183.6.
  - The extractor bound gives `q ≥ 1/4` on `U_n`.
  - The rejection law is a mixture, and it is an `(n−2)`-source.
  - Its acceptance probability is `1−(3/4)^11 = 4017157/4194304 > 3/4`, which contradicts the extractor bound `≤ 3/4`.
  - The edge cases `n = 0,1,2`, `q ∈ {0,1}` and empty output are covered.
- **Rule 10:**
  - All 28 seal records were reconciled.
  - The coe variant removes exactly `FinDist.instCoeFunForallReal`, so the projection-coercion ruling covers the strict Rejection errors.
  - The 12 controls reconcile, and the explicit scan has no foreign definition.
- **Facade:** the patch is exactly the two approved imports, and there is no import cycle.
- **LE-doc:** all 44 formulas are accurate.
- **Lint:** the auditor re-ran it and got 216 FAIL / 102 WARN, byte-identical at base and head.

## One observation recorded (not a finding)
The auditor notes that DL-39's list is shorter than the worker's full promotion list. The full list is in the delivery's `promotion-requests.md`, `rejection-review.md` and `sampler-review.md`, and includes `map_apply_expect`, `branch_apply`, the uniform-machine family and `take_poly`. The DL-39 ledger row now points to those files as the authoritative list.

## Disposition
No change is needed. **PR [#303](https://github.com/Shilun-Allan-Li/tcslib/pull/303)** is marked ready at `e99a6055`.
