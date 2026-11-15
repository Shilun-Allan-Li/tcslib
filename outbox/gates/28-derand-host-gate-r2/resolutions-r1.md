# Gate 28 · resolutions, round 1 · HOLD → round 2

Codex's verdict is **HOLD**: 0 blockers, 2 majors, 1 minor, 1 note.
- **Findings:** `findings/gate28-derand-host-findings.md`.
- **Audited head:** `8972fb4ef15fa3d4e3df37d6aa8674408835593d`.
- Codex found the mathematics sound. The contract is true, including ties, `w = 0`, `m = 0` and small `n`. It is
  sufficient for Theorem 180.1 by the full paper proof, which Codex rechecked. The route is feasible.

| # | Severity | Disposition |
|---|---|---|
| G28-01 | major | **To fix in records.** Register host **H17** in `machine-library-design.md` §14. The entry records the contract, home, reader, Gate 28 status, proof owner (the `derand` fill), consumers, route and the G28-02 disposition. It accompanies round 2. |
| G28-02 | major | **Ruling (Seyoon, 2026-11-15): add a machine-level contract.** #312 is revised to state a shared host contract that ties correctness, time and a coarse head envelope (derived from the time bound) to the **same machine**. `seedMajority_mem_DTIME` is kept as its corollary. The admitted `loopHostTM_*` space specs must not be used. Gate 28 then has a round 2. |
| G28-03 | minor | **To fix in round 2.** The consumer paragraph will give the piecewise test **and** width from the paper proof: true coins and `m(n)` below the threshold, `F'(u)↾m` and `ℓ(n)` from it on. |
| N28-01 | note | **To fix in round 2.** The proof owner is named consistently: the `derand` fill proves the host and the theorem. The `derand` brief, order and roots are updated after the gate, together with the two pre-approved shared-file changes. |

## Round-2 edits (head `0c04d1eb1e5450372632a23f3e94f3b7bfc37606`)

- **G28-01 · done.** H17 is registered in `machine-library-design.md` §14 (records), with a line in the status
  paragraph. The row gives the contract, its home, the reader, the gate status, the proof owner (the `derand` fill),
  the consumers, the route and the head-envelope clause. The draft is kept as `landing-r1/H17-row-draft.md`.
  - The registry row departs from the draft in one place: the corollary is recorded as admitted, as below.
- **G28-02 · done** by `2f9333b9`. The new existential contract `exists_seedMajorityTM` gives one machine `M`
  with constants `c, e` and two properties:
  - `M.DecidesInTime S (n ↦ c·(2^{w n}·(n+1)^e))`;
  - the head envelope `|workTapePos j| ≤ c·(2^{w|x|}·(|x|+1)^e)` for every input, time and tape. This is H14's
    `Clean.envelope` form, derived from the time bound. No admitted space spec is used.
  - The contract stays sorried for the `derand` fill.
- **The corollary · admitted** (`0c04d1eb`). Round 2 first proved `seedMajority_mem_DTIME` from the contract. That
  proof read `FinTM.DecidesInTime` and `DecidesInTimeVia` by their definitions, which Rule 10 forbids, so the
  maintainer reverted it to `sorry`.
  - It follows from the contract through the reader `mem_DTIME_iff`. The `derand` fill adds that reader under its
    pre-approval, and proves the corollary as well.
  - The whole-file seal now also seals `DecidesInTime`, `DecidesInTimeVia` and `DTIME`, and passes.
  - The paired controls, two of them new, each fail exactly once sealed.
- **G28-03 · done.** The consumer paragraph gives the piecewise test and width.
- **N28-01 · done.** The proof owner is named consistently: the `derand` fill proves the contract, the corollary
  and Theorem 180.1.
- **Build and lint.** 63/63 modules give rc 0 through root `TCSlib`. The only `sorry`s are the contract and the
  corollary. Lint is unchanged: Cryptography 92/101, Complexity 25/391.
- **Evidence.** In `landing-r1/`:
  - `stmt-derand-r2-evidence.zip`, SHA-256 `80123d3de4f30fda800b5b85d1ac6bd6f07c0c231e5660fd61c5ad3693071183`;
  - `stmt-derand-r2b-evidence.zip`, SHA-256 `146953211c64a6219b427712154fd8effc4004c8dae024f6c625c56f8a0c09cd`.

Round 2 of Gate 28 goes to Codex next.
