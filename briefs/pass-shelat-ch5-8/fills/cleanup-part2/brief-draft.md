# Worker brief (DRAFT, not issued): gate 03 clean-up, part 2 (ch. 2–4)

**Status: draft, 2026-11-05.** Issued after gate 04 closes and #195 (S2b) merges into
`cryptography/pass-shelat-ch2-4`. Part 1 is #203 (merged).

**Before issue:**
- the base is the branch head after #195's merge;
- gate 04 round 4's **seal exclusions** (inherited ch. 2–4 proofs that read other files'
  definitions, listed by the repair worker in `exclusions.md`) are copied into item J below;
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
- **DL-11, second half:** re-point the `stateFind` copies (`GI.stateFind`,
  `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, the variant
  `stateIterate`) to `Complexity.polyTimeComputable_stateFind` and delete them. Remove their
  "private" docstrings (`EncodingMachines.lean:468`, `GI/Efficiency.lean:47, 83–84`,
  `GGMReduction.lean:258`). Un-qualify `ThreeColoring/Machines.lean:126`.
- **DL-12 `abs_uexp_sub_le`, DL-14 `forall_of_uprob_eq_one`:** one public copy each.
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
- `NUPPT.coinLen_eq : A.coinLen n = A.coins.eval n`;
- `NUPPT.advInput_eq : A.advInput n y = pairEncode (List.replicate n true) y`;
- `NUPPT.runAtL_eq` (its defining equation).

Then re-point `Closure.lean`'s `simp [runAtL, advInput, coinLen, …]` sites to them, including
`exists_comp` and `exists_compParam`. These are prerequisites of the efficiency fill
(`fills/efficiency/brief-draft.md`, "Prerequisites").

**D. `decodeOracleMove`'s case lemmas** (`Asymptotic/PRF.lean`), public, beside the definition:
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

**J. Gate 04's seal exclusions** (`gates/04-s2b/evidence-r4/exclusions.md`: section A, 48 definitional reads; section B, 75 explicit unfolds; all in inherited ch. 2–4 declarations): re-prove the listed inherited ch. 2–4 proofs
through published equation lemmas, adding missing equation lemmas beside their definitions.

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

**Out of scope:** DL-20 (`Loop.lean`'s `loop_first_halt`; at the `main` landing). Statements change
only where an item says so.

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
