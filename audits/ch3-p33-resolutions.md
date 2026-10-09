# Chapter 3, phase P3.3 (NDTM codes, the linear-overhead universal, Theorem 3.2) — audit loop resolutions

**Gate: CLOSED (round 2, 2026-10-09).** Two rounds:

| Round | Verdict | Findings files |
|---|---|---|
| 1 | FAIL — 0 blockers, 2 majors, 7 minors, 2 notes | `audits/ch3-p33-findings.md` |
| 2 | **PASS — 0 blockers, 0 majors, 2 minors, 2 notes** | `audits/ch3-p33-r2-findings.md` |

No literal statement was ever refuted in this loop; both majors lived in
`ntime_hierarchy`'s proof sketch.

## The loop

* **Round 1's majors**: (1) the sketch absorbed per-code universal
  constants by "picking a padded large index" — invalid, since padding
  preserves `decode` but no law preserves cost; (2) the stage ladder was
  not an executable locator (existential BF coefficients are not
  computable stage data). Repaired by the rebuilt construction: the
  **fixed-code stage schedule** `i = pair(j, r)` (every code recurs; the
  alleged decider's constants are fixed along its own subsequence), the
  **`f`-adaptive tower ladder** `T*_i := (f a + a + 1)²`,
  `ℓ_{i+1} := 2^{(T*_i)²}` located by bit-length arithmetic with **capped
  witness runs whose failure itself decides the comparison**, and the
  **self-clocked** interpreter core under `D`'s own uniform
  `K·(g n + 1)` countdown with cut branches rejecting.
* **Round 2**: PASS. The auditor verified the fixed-code quantifier order,
  built the concrete `O(n)` capped locator (no monotonicity of either
  bound needed), and confirmed the middle/top comparisons give the
  contradiction after a fixed setup/clock allowance.

## Minors, swept in the closing commit and re-verified

| # | Sweep |
|---|---|
| 1 | The ladder is pinned as **the** sequence: seeded at `ℓ₀ := 2`, lengths at or below the seed rejected, the source formula `(f a + a + 1)²` authoritative. **Pack erratum acknowledged** (shipped packs are never edited): the round-2 pack's paraphrase `(f(ℓᵢ+1)+ℓᵢ+1)²` differs from the source formula by an offset |
| 2 | The clock ledger states the allowance split: a fixed share reserved ahead of simulation for the one `g`-witness run (bounded by its own clause, not cut by the yet-unbuilt countdown), budget/countdown preparation, and the worst single binary borrow; the interpreter core carries a named **prefix-bound obligation** |

Also applied with note 3's disposition: the stage-bottom comparison is
attributed to the square against fixed constants (no `g a` comparison);
the hypothesis's `f n` addend serves the inclusion half.

## Earlier pack erratum (round 1, acknowledged)

The round-1 pack asserted `g 0 = 0` is impossible under
`TimeConstructible`; `timeConstructible_id` refutes this (round-1 finding
8). The `g + 1` rendering and the explicit `hpos` hypothesis stand, as in
the deterministic precedent.

## Carried into the fill briefs

* The schedule/unranking, the seeded ladder with the capped-comparison
  locator and its amortized ledger, the self-clocked interpreter core at
  fixed `K` with the prefix bound, both transfer instantiations (`f(n+1)`
  mid-rung, `f a` at stage bottoms — the square), and the chain induction.
* The `2 · 27`-record ND parser with its `702·(numStates+1)` guard; the
  amortized countdown (`Σ ν₂(j) ≤ t`, significant-end representation); the
  `(k+1)(t+1)` normal-form ledger; the auditor's suggested sanity lemmas
  (zero-step non-acceptance, accept-at-any-time iff accept-at-`T` under
  halting, `workPair` injectivity, the round-trip parse).

## Consequences

* **The chapter-3/4 statement program's drafted phases are now fully
  gated**: P0, P3.1, P3.2, P3.3, P4.1, P4.2, P4.3, P4.4 all CLOSED; only
  the §12 routine layer remains in its loop, and P3.4 (Ladner) remains to
  draft.
* `NDCodes` joins the `TuringMachine.lean` facade and `NTimeHierarchy` the
  `Diagonalization.lean` facade; the root's temporary imports are removed.
* Statement-freeze baseline: the closing commit.
