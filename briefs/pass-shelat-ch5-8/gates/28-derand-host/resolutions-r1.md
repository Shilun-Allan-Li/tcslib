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
