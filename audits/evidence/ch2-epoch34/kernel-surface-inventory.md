# Reviewed kernel-surface inventory — the six owned modules (round 3)

Generated from the round-2/3 verification snapshot (sources byte-identical
to `audits/evidence/ch2-epoch34/final-source-manifest.md`, asserted before
the run) by enumerating every checked kernel declaration whose name is
non-private, with no `isInternal` exemption and no prefix inference. Every
name below is bound to its class and generating declaration; the round-3
program `audits/programs/ch2-epoch34-R3Axioms.lean` embeds exactly these 87
names and asserts two-directional set equality per module. The round-2
disclosure undercounted the SAT instance family (3 of its 7 members; the
four `._proof_N` members were masked by the `isInternal` exemption the
auditor rejected) — corrected here in full.

## `TCSlib.Complexity.ClassNP.Nondeterminism` — 15 names

- `Complexity.EXP_eq_NEXP_of_P_eq_NP` — **source public** (declared in this module)
- `Complexity.NEXP_eq_iUnion_NTIME` — **source public** (declared in this module)
- `Complexity.NEXP_subset_iUnion_NTIME` — **source public** (declared in this module)
- `Complexity.NP_eq_iUnion_NTIME` — **source public** (declared in this module)
- `Complexity.NP_subset_iUnion_NTIME` — **source public** (declared in this module)
- `Complexity.P_ne_NP_of_EXP_ne_NEXP` — **source public** (declared in this module)
- `Complexity.ntime_expPow_subset_NEXP` — **source public** (declared in this module)
- `Complexity.ntime_expPow_subset_NEXP._proof_1_2` — proof-extraction auxiliary auto-generated for the source public `Complexity.ntime_expPow_subset_NEXP`
- `Complexity.ntime_expPow_subset_NEXP._proof_1_3` — proof-extraction auxiliary auto-generated for the source public `Complexity.ntime_expPow_subset_NEXP`
- `Complexity.ntime_expPow_subset_NEXP._proof_1_4` — proof-extraction auxiliary auto-generated for the source public `Complexity.ntime_expPow_subset_NEXP`
- `Complexity.ntime_poly_subset_NP` — **source public** (declared in this module)
- `Turing.NDTM.runWith.eq_1` — equation lemma auto-generated in this module for the imported public definition `Turing.NDTM.runWith` (TuringMachine/Nondeterministic.lean:129); a definitional restatement, no new claim
- `Turing.NDTM.runWith.eq_2` — equation lemma auto-generated in this module for the imported public definition `Turing.NDTM.runWith` (TuringMachine/Nondeterministic.lean:129); a definitional restatement, no new claim
- `Turing.NDTM.runWith.eq_def` — equation lemma auto-generated in this module for the imported public definition `Turing.NDTM.runWith` (TuringMachine/Nondeterministic.lean:129); a definitional restatement, no new claim
- `Turing.NDTM.stepWith.eq_1` — equation lemma auto-generated in this module for the imported public definition `Turing.NDTM.stepWith` (TuringMachine/Nondeterministic.lean:115); a definitional restatement, no new claim

## `TCSlib.Complexity.ClassNP.EXP` — 22 names

- `Complexity.EXP` — **source public** (declared in this module)
- `Complexity.EXP_subset_NEXP` — **source public** (declared in this module)
- `Complexity.ExpBound` — **source public** (declared in this module)
- `Complexity.NEXP` — **source public** (declared in this module)
- `Complexity.NP_subset_EXP` — **source public** (declared in this module)
- `Complexity.NP_subset_EXP._proof_1_1` — proof-extraction auxiliary auto-generated for the source public `Complexity.NP_subset_EXP`
- `Complexity.NP_subset_EXP._proof_1_2` — proof-extraction auxiliary auto-generated for the source public `Complexity.NP_subset_EXP`
- `Complexity.NP_subset_EXP._proof_1_3` — proof-extraction auxiliary auto-generated for the source public `Complexity.NP_subset_EXP`
- `Complexity.NP_subset_EXP._proof_1_4` — proof-extraction auxiliary auto-generated for the source public `Complexity.NP_subset_EXP`
- `Complexity.NP_subset_EXP._proof_1_5` — proof-extraction auxiliary auto-generated for the source public `Complexity.NP_subset_EXP`
- `Complexity.P_subset_EXP` — **source public** (declared in this module)
- `Complexity.P_subset_EXP._proof_1_1` — proof-extraction auxiliary auto-generated for the source public `Complexity.P_subset_EXP`
- `Complexity.enumWord` — **source public** (declared in this module)
- `Complexity.enumWord._sunfold` — smart-unfolding auxiliary auto-generated for the source public `Complexity.enumWord`
- `Complexity.enumWord._unsafe_rec` — partial-recursive implementation companion (Lean's `addAndCompilePartialRec`) auto-generated for the source public `Complexity.enumWord`
- `Complexity.enumWord.eq_1` — equation lemma auto-generated for the source public `Complexity.enumWord`
- `Complexity.enumWord.eq_2` — equation lemma auto-generated for the source public `Complexity.enumWord`
- `Complexity.enumWord.eq_def` — equation lemma auto-generated for the source public `Complexity.enumWord`
- `Complexity.enumWord.match_1` — match auxiliary auto-generated for the source public `Complexity.enumWord`
- `Complexity.exists_proj_decider` — **source public** (declared in this module)
- `Complexity.exists_proj_decider._proof_1_1` — proof-extraction auxiliary auto-generated for the source public `Complexity.exists_proj_decider`
- `Turing.solveSplitWith.eq_1` — equation lemma auto-generated in this module for the imported public definition `Turing.solveSplitWith` (TuringMachine/Build/Convention.lean:130); a definitional restatement, no new claim

## `TCSlib.Complexity.ClassNP.SAT` — 15 names

- `Complexity.SAT` — **source public** (declared in this module)
- `Complexity.SAT3` — **source public** (declared in this module)
- `Complexity.SAT3_mem_NP` — **source public** (declared in this module)
- `Complexity.SAT_mem_NP` — **source public** (declared in this module)
- `Complexity.SAT_reducible_SAT3` — **source public** (declared in this module)
- `Complexity.instDecidableEqSatStreamState` — member of the `deriving DecidableEq` family of the **private** `structure SatStreamState` (SAT.lean:2301); a non-private generated constant whose type mentions the private structure (derive-handler naming)
- `Complexity.instDecidableEqSatStreamState.decEq` — member of the `deriving DecidableEq` family of the **private** `structure SatStreamState` (SAT.lean:2301); a non-private generated constant whose type mentions the private structure (derive-handler naming)
- `Complexity.instDecidableEqSatStreamState.decEq._proof_1` — member of the `deriving DecidableEq` family of the **private** `structure SatStreamState` (SAT.lean:2301); a non-private generated constant whose type mentions the private structure (derive-handler naming)
- `Complexity.instDecidableEqSatStreamState.decEq._proof_2` — member of the `deriving DecidableEq` family of the **private** `structure SatStreamState` (SAT.lean:2301); a non-private generated constant whose type mentions the private structure (derive-handler naming)
- `Complexity.instDecidableEqSatStreamState.decEq._proof_3` — member of the `deriving DecidableEq` family of the **private** `structure SatStreamState` (SAT.lean:2301); a non-private generated constant whose type mentions the private structure (derive-handler naming)
- `Complexity.instDecidableEqSatStreamState.decEq._proof_4` — member of the `deriving DecidableEq` family of the **private** `structure SatStreamState` (SAT.lean:2301); a non-private generated constant whose type mentions the private structure (derive-handler naming)
- `Complexity.instDecidableEqSatStreamState.decEq.match_1` — member of the `deriving DecidableEq` family of the **private** `structure SatStreamState` (SAT.lean:2301); a non-private generated constant whose type mentions the private structure (derive-handler naming)
- `Std.Sat.CNF.WidthAtMost.eq_1` — equation lemma auto-generated in this module for the imported public definition `Std.Sat.CNF.WidthAtMost` (Formulas/CNFEncoding.lean); a definitional restatement, no new claim
- `Std.Sat.CNF.fallback.eq_1` — equation lemma auto-generated in this module for the imported public definition `Std.Sat.CNF.fallback` (Formulas/CNFEncoding.lean:158); a definitional restatement, no new claim
- `Std.Sat.CNF.numVars.eq_1` — equation lemma auto-generated in this module for the imported public definition `Std.Sat.CNF.numVars` (Formulas/CNFEncoding.lean); a definitional restatement, no new claim

## `TCSlib.Complexity.CookLevin.Snapshot` — 24 names

- `Complexity.Snapshot` — **source public** (declared in this module)
- `Complexity.emitted` — **source public** (declared in this module)
- `Complexity.inputBitAt` — **source public** (declared in this module)
- `Complexity.inputBitAt.eq_1` — equation lemma auto-generated for the source public `Complexity.inputBitAt`
- `Complexity.inputPosAt` — **source public** (declared in this module)
- `Complexity.oblivious_schedule_eq` — **source public** (declared in this module)
- `Complexity.prevVisit` — **source public** (declared in this module)
- `Complexity.snapshotAt` — **source public** (declared in this module)
- `Complexity.snapshotAt.eq_1` — equation lemma auto-generated for the source public `Complexity.snapshotAt`
- `Complexity.snapshotAt_inputSymbol` — **source public** (declared in this module)
- `Complexity.snapshotAt_inputSymbol._proof_1_2` — proof-extraction auxiliary auto-generated for the source public `Complexity.snapshotAt_inputSymbol`
- `Complexity.snapshotAt_inputSymbol._proof_1_3` — proof-extraction auxiliary auto-generated for the source public `Complexity.snapshotAt_inputSymbol`
- `Complexity.snapshotAt_state_succ` — **source public** (declared in this module)
- `Complexity.snapshotAt_workSymbol` — **source public** (declared in this module)
- `Complexity.snapshotAt_workSymbol._proof_1_1` — proof-extraction auxiliary auto-generated for the source public `Complexity.snapshotAt_workSymbol`
- `Complexity.snapshotAt_workSymbol._proof_1_2` — proof-extraction auxiliary auto-generated for the source public `Complexity.snapshotAt_workSymbol`
- `Complexity.snapshotAt_workSymbol.match_1` — match auxiliary auto-generated for the source public `Complexity.snapshotAt_workSymbol`
- `Complexity.snapshotAt_zero` — **source public** (declared in this module)
- `Complexity.stepState` — **source public** (declared in this module)
- `Complexity.stepState.eq_1` — equation lemma auto-generated for the source public `Complexity.stepState`
- `Complexity.stepState.match_1` — match auxiliary auto-generated for the source public `Complexity.stepState`
- `Complexity.workPosAt` — **source public** (declared in this module)
- `Complexity.writtenOrKept` — **source public** (declared in this module)
- `Complexity.writtenOrKept.eq_1` — equation lemma auto-generated for the source public `Complexity.writtenOrKept`

## `TCSlib.Complexity.ClassNP.Tautology` — 6 names

- `Complexity.TAUTOLOGY` — **source public** (declared in this module)
- `Complexity.TAUTOLOGY_coNPComplete` — **source public** (declared in this module)
- `Complexity.TAUTOLOGY_coNPComplete._simp_1_1` — simp auxiliary lemma auto-generated for the source public `Complexity.TAUTOLOGY_coNPComplete`
- `Complexity.TAUTOLOGY_mem_coNP` — **source public** (declared in this module)
- `Complexity.coNPComplete` — **source public** (declared in this module)
- `Complexity.coNPHard` — **source public** (declared in this module)

## `TCSlib.Complexity.CookLevin.Hardness` — 5 names

- `Complexity.NPHard.polyTimeReducible` — **source public** (declared in this module)
- `Complexity.SAT3_NPComplete` — **source public** (declared in this module)
- `Complexity.SAT3_NPHard` — **source public** (declared in this module)
- `Complexity.SAT_NPComplete` — **source public** (declared in this module)
- `Complexity.SAT_NPHard` — **source public** (declared in this module)

**Total: 87 names** = 45 source publics + 27 generated auxiliaries of
source publics + 8 imported-definition equation lemmas + the 7-member
derived-instance family of a private structure.

---

## Round-3 closing correction (finding 3 and note 4, swept at gate close)

The seven `instDecidableEqSatStreamState` rows originally claimed the family
was “unusable downstream.” The round-3 auditor refuted that rationale with a
compiling consumer (aliasing the instance, recovering the type through an
instance argument, and invoking it), so the rows above now state only the
facts: non-private generated constants whose types mention a private
structure. All seven remain in the certified inventory. The
`enumWord._unsafe_rec` class wording was refined per the same report.
