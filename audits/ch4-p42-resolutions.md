# Chapter 4, phase P4.2 (configuration graphs and Savitch) — audit loop resolutions

**Gate: CLOSED (round 1, 2026-10-08).** One round: **PASS — 0 blockers,
0 majors, 5 minors, 3 notes** (`audits/ch4-p42-findings.md`, verbatim). All 5
definitions blind-restated clean; all 10 sorried statements accepted with
independent derivations — including the exact three-class minimality proof
for the `OutSummary` quotient, the full splice/pad argument with the window
side condition made explicit, the complete exponent ledger for the
exponential-time simulation (vertex count, constructor cost through the
received deterministic count theorem, and sequential-access table
accounting), the base-case-corrected midpoint recurrence for Savitch, and
both constant absorptions of `PSPACE_eq_NPSPACE` with explicit multipliers.
The bundle hash was independently recomputed; 15 adversarial instantiations
ran, including a 12,645-case finite model of the append-summary table.

## Minors, swept in the closing commit and re-verified

| # | Sweep |
|---|---|
| 1 | `acceptsWithin_of_spaceUsedWith_le`'s sketch no longer asserts that padded **siblings** stay halted (the statement has no sibling-halting hypothesis — the auditor's two-choice counterexample has a live all-`true` branch): it is the accepting branch that stays halted under padding, and nothing else is needed |
| 2 | `polyTimeReducible_of_mem_NL`'s docstring now records the **textbook erratum** explicitly: Exercise 4.3's printed wording says "complete for `NL`", which is false for arbitrary nontrivial targets (an undecidable target defeats completeness); the theorem claims hardness, and completeness additionally requires `L ∈ NL` |
| 3 | `configBound`'s docstring cites the received deterministic count by its real name, `Turing.FinTM.configBound` (not `Turing.MultiTapeTM.ConfigCount.configBound`) |
| 4 | `NL_subset_P`'s sketch no longer calls the received `LOGSPACE_subset_P` "the deterministic special case of the same search": that proof keeps the original machine and bounds its halting time through `ComputesInSpace`, building no search or table — the shared ingredient is the count arithmetic |
| 5 | `NSPACE_subset_exp_dtime`'s prose no longer claims the `+ 1` "keeps the exponent positive" (the `c = 0` component has exponent `0`): the time bound is everywhere positive regardless, and the `+ 1`'s job is the input-head absorption |

Re-verification: `ConfigGraph` and `Savitch` re-elaborate with zero errors
(10 `sorry` warnings exactly); the pack's question 3 carried the same
sibling-halting slip as the sketch — a **pack erratum, acknowledged here**
(shipped packs are never edited).

## Notes (dispositions recorded)

* **Note 6 (carrier bridge)**: `CfgStep` relates full configurations while
  the counting lives on windowed summary vertices. Carried verbatim into the
  fill briefs: canonical decoding, outside-window edge rejection, quotient
  path lifting from the true initial configuration, enumeration of accepting
  vertices (no unique-target assumption), and the reflexive base case of
  bounded reachability.
* **Note 7 (resource ledgers)**: the constructor's exponential **time** bound
  flows through the received `Turing.FinTM.ComputesInTime.of_spaceUsed_le`
  (not circular — deterministic, received); Savitch's frames must reuse
  **fixed physical tape intervals** under the visited-cell measure; the
  polynomial constructor must emit exactly `(n^c + 1).bits`, including the
  final `+ 1` and the `n = 0` case. All carried into the fill briefs.
* **Note 8 (attestation posture)**: revision identity, the prose-only
  landing comparison, and olean freshness remain maintainer attestations;
  recorded, no action.
* **Cross-filed from concurrent rounds**: the P4.3 round's note 10 and the
  P4.4 round's note 7 both examined this phase's `coreSum`/`CfgStep`
  declarations and found no defect, flagging only the carrier-bridge
  distinction already carried as note 6 here. The P4.3 round's blocker is a
  P4.3-side misuse of the finite-counting idea (full-configuration codec),
  not an inherited defect of this surface.
* **Auditor-supplied constructions banked for fill**: the sequential-access
  BFS ledger (no unit-cost lookup assumed), the min/max-interval overflow
  observation, the `2a ≤ a² + 1` absorption chain, and the suggested additive
  sanity lemmas (`outSummary` append table, iterated `coreSum_stepWith`,
  `¬ AcceptsWithin x 0`, tape-count lower bound, bounded-code lifting).

## Consequences

* The `SpaceComplexity` surface of this phase is **closed**; the P4.4 gate
  (closed the same day) consumes it, and the open P4.3 repair round re-states
  its codec over this phase's `coreSum` quotient exactly as this round's
  design intended.
* Statement-freeze baseline for the closed surface: the closing commit
  (minors are docstring/sketch prose only; no declaration changed).
