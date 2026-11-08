**Historical design draft — superseded by [issued r1](issued-r1/brief.md), prepared for one Claude session.**

# Worker brief (DRAFT, not issued): gate 03 clean-up, part 2 (ch. 2–4)

**Status: preparation draft, not issued; refreshed 2026-11-07 PST.** Part 1/#203, #195,
S1/#227 and S2/#231 are merged. Post-S2 source prerequisite: `1aa5506f58f77c215e56d24311ec33bd931cacf1`.
**Worker selected by the user: Claude**, checkpoint/final payloads pushed only to the assigned
exchange subtree; campaign changes land through a PR the user merges. Reconciliation,
pre-ship probes and internal brief review remain before issue. Gate 06 audits stay frozen on
their separate pre-S2 source; this fill must not edit their branch or rely on unmerged APIs.

**Before issue:**
- the base is the branch head after #195, S1 (#227) and S2 have merged;
- reconcile item J and item N's untouched-proof rows against that base: gate 04 round 5 has
  **zero exclusions**, and work already done by #195, S1 or S2 is not commissioned again;
- the line numbers below are refreshed at the base;
- the brief is split if two workers run in parallel. The natural split is DL-17 (item B, about 23
  files) against the rest, on disjoint files;
- the order list and the base sorry set are recorded.

## Scope

**A. Duplicated private helpers (G3-5 (A); ledger rows; reviews 03a #4, #8 and 03b #12):**
- **DL-9 `blocks`:**
  - one public coin-block bijection `FunFamily.blocks` (`Fin (m · c) → Bool ≃ Fin m → Fin c →
    Bool`), with its lemmas, in a low file;
  - the copies `OneWayYao.blocksE`, `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks`,
    `SoundnessRep.blocksEquiv` and the private `Ensemble.blocks` (`Asymptotic/Ensembles.lean`,
    gate 03a round 2, R2-4) deleted, and their users re-pointed;
  - S2b's public duplicate `take_drop_ofFn_blocks` folded into
    `EnsembleLemmas.take_drop_ofFn_blocks` (gate 04 N4).

  This changes **statements** of packs 03h, 03i and 03k: list each old → new.
- **DL-10 `ptc_comp`:** one public form in `Randomized/Closure.lean`; the six copies (`Closure` and
  `Repetition` helpers, `Universal*`, `ThreeColoring/Machines`, …) deleted.
  **Update 2026-11-07 (shared-lemma rulings Q2 (A)):** the shared-lemma PR S1 publishes
  `PolyTimeComputable.comp'`/`.congr` in `Closure.lean`. This item reduces to deleting `Closure`'s
  private `ptc_comp`, re-pointing its 27 uses, and re-pointing the other G6 copies
  (`fills/shared-lemmas/design.md` §5.4). Base `ptc_congr`s take the reversed hypothesis
  (`fun w => (h w).symm`).
- **DL-11, second half:** re-point the `stateFind` copies (`GI.stateFind`,
  `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, the variant
  `stateIterate`) to `Complexity.polyTimeComputable_stateFind` and delete them. Remove their
  "private" docstrings (`EncodingMachines.lean:468`, `GI/Efficiency.lean:47, 83–84`,
  `GGMReduction.lean:258`). Un-qualify `ThreeColoring/Machines.lean:126`.
- **DL-12 `abs_uexp_sub_le`:** done by the shared-lemma PR S1 (dropped here). **DL-14
  `forall_of_uprob_eq_one`:** one public copy.
- **DL-13:** delete `ZeroKnowledge/Defs.lean`'s `negligible_const_zero` (2 uses) in favour of
  `negligible_zero`.
- **DL-15:** one public `decodeFin_eq_some_iff` in `Asymptotic/Adversary.lean`, avoiding the
  clash with `GGMRed.decodeFin_eq_some_iff` (public, `GGMReductionEval.lean`); the forward lemma
  `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`) derived from it; S2b's private
  `eq_ofFn_of_decodeFin` folded into it.

**B. DL-17 (R-03l-1): `StateLoop`'s restatements of `main`'s lemmas.** Per gate 03l review §6.1 (c),
delete the restatements and re-point their users (about 23 files in packs 03a, 03c, 03e, 03f2 and
03g–03k, including #195's `PRFLemmas`, `MultiMessageLemmas` and `GraphIsomorphism/Efficiency*`):

| Restatement (`Randomized/Build/StateLoop.lean`) | `main`'s lemma |
|---|---|
| `headBit_poly` | `Complexity.polyTimeComputable_headD` (`ClassNP/PolyTimeBlockLoop.lean`) |
| `tail_poly` (`List.tail`) | `polyTimeComputable_tail` (`w.drop 1`; bridge `List.tail = drop 1`) |
| `isNil_poly` | `polyTimeComputable_isNil` |
| `not_poly` | `polyTimeComputable_not` |
| `or_poly` | `polyTimeComputable_or` |
| `xor_poly` | `BinArith.polyTimeComputable_xor` (`ClassP/BinaryArith/Basic.lean`) |
| `length_pairFstD_add_pairSndD_le` | follows from `length_pair_components_le` |

`cons_poly` is an alias without a duplicated proof; keep it.

**C. Equation lemmas in `PPT.lean`:**
These are already public at the Codex intake base `3ee2c5b28266d986dfce46f25fd4989de861b96e`.
Verify and cite them at the issue base; do not add duplicate declarations:
- `NUPPT.coinLen_eq : A.coinLen n = A.coins.eval n`;
- `NUPPT.advInput_eq : A.advInput n y = pairEncode (List.replicate n true) y`;
- `NUPPT.runAtL_eq` (its defining equation).

Then re-point `Closure.lean`'s `simp [runAtL, advInput, coinLen, …]` sites to them, including
`exists_comp` and `exists_compParam`. These are prerequisites of the efficiency fill
(`fills/efficiency/brief-draft.md`, "Prerequisites").

**D. `decodeOracleMove`'s case lemmas** (`Asymptotic/PRF.lean`), public, beside the definition:
Reuse #195's public `decodeOracleMove_pairEncode_false` and `decodeOracleMove_true_two`
(verified at `9ac1c4260adb8fbfe8c6f50df7786dbdd015656e`). Add only forms still missing at
the issue base, with coverage for all four cases below:
- `⟨[false], x⟩` with `|x| = ℓ₁` decodes as `query x`;
- `⟨[false], x⟩` with `x` of any other length decodes as `ret false`;
- `[true, b]` decodes as `ret b`;
- anything else decodes as `ret false`.

The private `decodeOracleMove_eq` is folded in. This is an efficiency fill prerequisite (T4).

**E.** `ThreeColoring/SimulatorMachine` imports `Randomized/NonUniform` itself; until now it got it
through the facade (03a #12).

**F.** The five `| zero => rfl` reads of `StateLoop.orbit`: `EncodingMachines.lean:572`,
`GI/Efficiency.lean:141`, `GI/EfficiencyRep.lean:194, 388`, `GGMReductionEval.lean:534`. They go
through `orbit_zero`.

**J. Inherited rule-10 reads.** Gate 04 round 5 has no exclusions. Round 4's historical
`gates/04-s2b/evidence-r4/exclusions.md` (48 definitional reads and 75 explicit unfolds) is an
input to reconciliation, not an outstanding exclusion list. Use item N's 764 untouched-proof
rows and the fill reviews as the current inventory; remove rows already repaired by #195,
S1 or S2, and commission each remaining declaration once. Re-prove those consumers through
published equation lemmas, adding missing equations beside their definitions.

**Gate 04 round 5, inherited core unfolds:** replace the four explicit `Function.comp`
arguments in `Asymptotic/MultiMessage.lean` and `MultiMessageLemmas.lean` by the published
equation `Function.comp_apply` (or a verified equivalent lemma-based proof). These are outside
the TCSlib-only scanner. Locations and a proposed, **not yet Lean-checked** patch are in
`gates/04-s2b/evidence-r5-review/{inherited-core-unfolds.tsv,core-comp-equations.diff}`.
Check the four proofs at the issue/landing tree; do not mistake the prepared patch for a repair
already on #195.

**K. Docstring (gate 03e round 3, minor 1).** In `ZeroKnowledge/Defs.lean`'s D8 deviation paragraph,
replace "the rewinding simulators of the chapter are truncated and the theorems become statistical"
with: expected polynomial time is not formalized; GI uses a truncated simulator and obtains
statistical ZK, while 3COL remains computational ZK with statistical sampling and failure terms.

**L. Docstrings (gate 03g round 2, R2-1; gate 03l round 3, minor 1).**
- `ZeroKnowledge/ThreeColoring/Simulator.lean`, `col_zk`'s sketch (about lines 755–771): the
  hiding term `K ε_B(n)` applies only for `m > 0`; for `m = 0` and `n ≥ 1` there is one hiding gap,
  at most `ε_B(n) ≤ N² ε_B(n)`. Skip this if the 3-colouring fill has already rewritten the sketch.
- `TuringMachine/Build/ModuleHost.lean`, `Clean.envelope`'s docstring (about line 231): replace
  "The contract gives nothing sharper" with: this theorem deliberately publishes the coarse
  time-derived bound and exposes no module-specific envelope (the contract implies the factor-two
  bound `⌊B/2⌋`, since the head starts and ends at 0).
- **Gate 04 round 5, R5-03:** restore the complete formula docstrings of
  `Protocol.transcriptWith_eq` and `Protocol.outV_eq` in `ZeroKnowledge/Interaction.lean`,
  naming all inputs, tapes, the verifier-first flag and round count where present in the
  statement. Prepared docstring-only patch:
  `gates/04-s2b/evidence-r5-review/interaction-docstrings.diff`. Statements and proofs stay
  byte-identical; this patch is queued, not landed.

**M. Mathlib replacements (DL-21; user direction 2026-11-06).** The DUP and WRAP rows of
`mathlib-overlap-nt.md` in `NumberTheory/*` and in files no fill owns: replace by the Mathlib
statement (keep a load-bearing name as a one-line alias) or shorten the proof as the probe log
shows. Rows in `Candidates/*` wait until those files' fills land. Statements change only where a
definition becomes a Mathlib alias: list each old → new.

**Out of scope:** DL-20 (`Loop.lean`'s `loop_first_halt`; at the `main` landing). Statements change
only where an item says so.

**N. Base re-points of the shared-lemma design's deferred groups (added 2026-11-07;
`fills/shared-lemmas/design.md` §5.4):**
- G7: `Language.lean`'s `h2`; `two_pow_permBits_le` as a corollary; keep one of
  `two_pow_size_le`/`two_pow_size_le_two_mul_succ` and re-point the other.
- G10: the `castLE` triple as corollaries of `HardcoreBit.pushesUniform_restrict`; `dlb_cut`;
  `pushesUniform_comp_injective` (after #195).
  **Gate 08 G10 interface note:** preserve the old nonempty-index theorem's extra
  empty-codomain case when re-pointing to the new generic theorem, which assumes `Nonempty O`;
  use a case split and retain the old statement. (This is the gate 08 findings' G10 note.)
- G13 (with DL-9), G14, G22 (with DL-11), G23, G25, and optionally G12 (after #195), and G18
  (`uexp_le_of_statClose`, deferred by Q5).
- The 764 untouched rule-10 rows recorded by #210 (`gates/07-eqlemmas/evidence-r2/r6c/cleanup-b*.tsv`),
  plus the final Gate 06 source-failure observations in
  `maintainer/gate06-integration-2026-11-06/evidence-rule10-final-r1/failure-disposition-r1/`:
  110 unchanged blocks / 138 diagnostics, 62 exact historical keys and 48 additional
  observation keys (the initial 35 plus 13 PolyTimeModel keys). Both newly scoped Encoding
  keys are historical; exact `_root_` normalization corrects the immutable witness
  proposal's 61/49 split. Preserve all original failures and prior surveys. The three C3
  pairs, 134 inherited TCSlib explicit candidates (three exact notation exceptions) and
  18 non-TCS explicit hits have separate retained records; these units overlap and must not
  be added as counts. Deduplicate at the post-S2 issue base; do not add 48 blindly to the
  historical 764-row count or treat inventory additions as repairs;
  and the base reads the fill reviews named: `primesPairEquiv_apply_val`, `exists_fullLengthExcept`,
  `rabinCollection_index`, `rabinBlumTrapdoor_index`.
- **Item M (DL-21)** runs after S2's landing, so that the two do not edit the same `Candidates`
  proofs.

## Checks (as part 1)

1. The replay of everything downstream of the changed files, with `downstream2.py`, and then
   `Checks`. `sorry` counts must equal the base's.
2. Full axiom prints of the changed files.
3. A seal of every consumer file touched, with candidates collected automatically (as in gate 04
   round 4) and controls.
4. `style_lint.py` and `campaign_style_lint.py --check8b`.
5. A statement diff (old → new for 03h, 03i, 03k's `blocks` statements).

Then packs 03h, 03i and 03k are re-staged and dispatched, and 03d and 03j are staged at the same
head.
