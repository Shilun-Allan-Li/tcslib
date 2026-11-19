# Efficiency wave 1: rulings (Seyoon, 2026-11-18)

All recommended options accepted. Binding on every wave-1 job; precedence: this file > the job's dispatch prompt >
its brief > COMMON.md.

- **Q-W1-1 (A):** the sampler-contract commit `foundations/coin-contract` (`8e01b720`) gets its own PR now,
  stacked on #378.
- **Q-H1-1 (A):** `PrimesInP` is `Randomized.PRIMESBin ∈ Complexity.P`, with the bridge to `primeStr` proved.
- **Q-D4-1 (A):** [PW10] §3.1–§3.2 are ingested by the maintainer before EF-D4 is dispatched.
- **Q-R-1 (A):** one worker for EF-R2 and EF-R3 (shared toolkit, three commit series).
- **Q-R-2 (A):** general modulus q.
- **Q-H11-1 (A):** Shamir, the resharer and the BGW gate steps now; the whole-circuit evaluator only on a
  registered host.
- **Q-H11-2 (A):** inverses mod p by Fermat via `BinArith.powMod` (precedent `DetMod`).
- **Q-H12-1 (A):** the route through circuits ([AB09, Lemmas 6.10, 6.11], public declarations only).
- **Q-H12-2 (A):** the maintainer ingests [AB09] ch. 2 and ch. 6 and a 3-colouring source before the delivery
  review; the worker cites the anchors the brief lists and flags anything unverified.
- **Q-H12-3 (A):** re-derive the private `sat3Coloring`, disclosed in REPORT.md; the course file stays read-only.
- **EF-D4-I (A)** (2026-11-18, after the [PW10] §3.1–§3.2 ingest): almost-always is the interface, exact is a
  strengthening with a proved `exact ⇒ almost-always`; consumers assume only almost-always; the brief
  discloses four specialisations (branch sets `{0,1}^{b(κ)}`, one bound uniform over branch pairs, `k ≤ n`
  stated, `NUPPT` distinguishers). Details in `EF-D4/brief.md`, *The interface ruling*.
