import Lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
run_cmd do
  let label : String := "FinalR2AveragingExtra_0_B"
  let payload : String := "TCSlib.Cryptography.Games.Bridge.acceptGame\tTCSlib.Cryptography.Games.Bridges.Experiments\nTCSlib.Cryptography.Games.OracleComp.AllOutputs\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.AllOutputs._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.AllOutputs._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp._sizeOf_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.bind\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.bind._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.bind._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.bind.match_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.call\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftLeft\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftLeft._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftLeft._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftLeft.match_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftRight\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftRight._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftRight._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleSpec._sizeOf_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleSpec.mk._flat_ctor\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.ProbComp.dist\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.expect\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.expect._sunfold\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.expect.match_1\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.prob\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.sample\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.sampleFin\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.accept\tTCSlib.Cryptography.Games.Advantage\nTCSlib.Cryptography.Games.advantage\tTCSlib.Cryptography.Games.Advantage\nTCSlib.Cryptography.Games.guessAdv\tTCSlib.Cryptography.Games.Advantage\nTCSlib.Cryptography.Games.guessGame\tTCSlib.Cryptography.Games.Advantage\nTCSlib.Cryptography.acceptProb\tTCSlib.Cryptography.Foundations.Experiments\nTCSlib.Cryptography.distAdv\tTCSlib.Cryptography.Foundations.Experiments\nTCSlib.Cryptography.invProb\tTCSlib.Cryptography.Foundations.Experiments\nTCSlib.Cryptography.predProb\tTCSlib.Cryptography.Foundations.Experiments\nTCSlib.Cryptography.uexp\tTCSlib.Cryptography.Foundations.Probability\nTCSlib.Cryptography.uprob\tTCSlib.Cryptography.Foundations.Probability\nTCSlib.InformationTheory.FinDist.HasMinEntropy\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist._sizeOf_1\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.collision\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.map\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.mk._flat_ctor\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.probTrue\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.prod\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.uniform\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.statDist\tTCSlib.InformationTheory.StatisticalDistance\n_private.TCSlib.Cryptography.Games.OracleComp.0.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1.splitter\tTCSlib.Cryptography.Games.OracleComp"
  let lines := if payload.isEmpty then [] else payload.splitOn "\n"
  unless lines.length == 50 do throwError "LAMP-HARNESS bad serialized count"
  let env ← Lean.getEnv
  let moduleNames := env.header.moduleNames
  let mut catalog : Std.HashMap String (Array Lean.Name) := {}
  for (n, _) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    unless (`TCSlib).isPrefixOf moduleNames[mi.toNat]! do continue
    catalog := catalog.insert n.toString (((catalog[n.toString]?).getD #[]).push n)
  let mut count : Nat := 0
  for row in lines do
    let [spelling, home] := row.splitOn "\t" | throwError "LAMP-HARNESS malformed row"
    let ns := (catalog[spelling]?).getD #[]
    unless ns.size == 1 do throwError "LAMP-HARNESS absent/ambiguous {spelling}"
    let n := ns[0]!
    let some mi := env.getModuleIdxFor? n | throwError "LAMP-HARNESS no home {spelling}"
    unless moduleNames[mi.toNat]!.toString == home do
      throwError "LAMP-HARNESS wrong home {spelling}"
    let some ci := env.find? n | throwError "LAMP-HARNESS no constant {spelling}"
    unless ci.isDefinition do throwError "LAMP-HARNESS not definition {spelling}"
    let before ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless before == .irreducible do
      let id := Lean.mkIdent n
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))
    let after ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless after == .irreducible do throwError "LAMP-HARNESS unsealed {spelling}"
    Lean.logInfo m!"LAMP-SEAL-NAME\t{label}\tINSTALL\t{spelling}\t{home}"
    count := count + 1
  unless count == 50 do throwError "LAMP-HARNESS wrong verified count"
  Lean.logInfo m!"LAMP-SEAL-INSTALL\t{label}\t{count}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Optional-query and fair-bit position averaging

## Main definitions

None.

## Main results

* `optionQuery_favourable_expect_ge`: fresh forged messages have favourable fraction
  at least `1 / (2 |I|)`, with or without a query.
* `exists_position_fairBit_expect_ge`: some fixed position with a fresh fair bit performs
  at least as well as a uniform position and bit.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 137.2. These are the counting and best-position steps of its reduction.
-/

namespace TCSlib.Cryptography.Authentication.LamportReduction

open TCSlib.Cryptography.Games

/-- If an optional queried message differs from the forged message, a uniform position and
bit avoids revealing the planted preimage and selects the forged preimage with probability
at least `1 / (2 |I|)`. An absent query imposes no avoidance constraint.
[PS10, proof of Theorem 137.2].

**Proof sketch.** With a query, freshness gives distinct messages and the differing-coordinate
bound applies. Without a query, half of the position-bit pairs select the forged preimage;
this is at least `1 / (2 |I|)` because the position type is nonempty. -/
theorem optionQuery_favourable_expect_ge {ι : Type} [Fintype ι] [Nonempty ι]
    (q : Option (ι → Bool)) (m' : ι → Bool) (hfresh : q ≠ some m') :
    1 / (2 * (Fintype.card ι : ℝ)) ≤
      ProbComp.expect (ProbComp.sample (ι × Bool))
        (fun p => if (∀ m, q = some m → m p.1 ≠ p.2) ∧ m' p.1 = p.2
          then (1 : ℝ) else 0) := by
  classical
  cases q with
  | none =>
    simp only [reduceCtorEq, false_implies, forall_const, true_and]
    rw [noQuery_expect_eq_half]
    have hcard : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card ι))
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  | some m =>
    have hne : m ≠ m' := by
      intro h
      exact hfresh (congrArg some h)
    simpa using (favourable_expect_ge hne)

/-- For every payoff `v(i,c)` on a nonempty finite position type and a bit, there is a
position whose average over a fair bit is at least the average over a uniform position and
fair bit. [PS10, proof of Theorem 137.2].

**Proof sketch.** Apply finite maximum averaging to the payoff already averaged over the bit.
The published product-sampling equation identifies its average over positions with the
uniform-pair expectation. -/
theorem exists_position_fairBit_expect_ge {ι : Type} [Fintype ι] [Nonempty ι]
    (v : ι → Bool → ℝ) :
    ∃ i, ProbComp.expect (ProbComp.sample (ι × Bool)) (fun p => v p.1 p.2) ≤
      ProbComp.expect (ProbComp.sample Bool) (v i) := by
  obtain ⟨i, hi⟩ := exists_expect_sample_le
    (fun j : ι => ProbComp.expect (ProbComp.sample Bool) (v j))
  refine ⟨i, ?_⟩
  calc
    ProbComp.expect (ProbComp.sample (ι × Bool)) (fun p => v p.1 p.2) =
        ProbComp.expect
          ((ProbComp.sample ι).bind fun j =>
            (ProbComp.sample Bool).bind fun c => .pure (j, c)) (fun p => v p.1 p.2) :=
      (Bridge.expect_sample_pair (fun p : ι × Bool => v p.1 p.2)).symm
    _ = ProbComp.expect (ProbComp.sample ι)
        (fun j => ProbComp.expect (ProbComp.sample Bool) (v j)) := by
      simp only [ProbComp.expect_bind, ProbComp.expect_pure]
    _ ≤ ProbComp.expect (ProbComp.sample Bool) (v i) := hi

end TCSlib.Cryptography.Authentication.LamportReduction

set_option maxHeartbeats 0
run_cmd do
  let label : String := "FinalR2AveragingExtra_0_B"
  let payload : String := "TCSlib.Cryptography.Games.Bridge.acceptGame\tTCSlib.Cryptography.Games.Bridges.Experiments\nTCSlib.Cryptography.Games.OracleComp.AllOutputs\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.AllOutputs._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.AllOutputs._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp._sizeOf_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.bind\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.bind._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.bind._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.bind.match_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.call\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftLeft\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftLeft._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftLeft._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftLeft.match_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftRight\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftRight._sunfold\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleComp.liftRight._unsafe_rec\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleSpec._sizeOf_1\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.OracleSpec.mk._flat_ctor\tTCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.ProbComp.dist\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.expect\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.expect._sunfold\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.expect.match_1\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.prob\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.sample\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.ProbComp.sampleFin\tTCSlib.Cryptography.Games.Probability\nTCSlib.Cryptography.Games.accept\tTCSlib.Cryptography.Games.Advantage\nTCSlib.Cryptography.Games.advantage\tTCSlib.Cryptography.Games.Advantage\nTCSlib.Cryptography.Games.guessAdv\tTCSlib.Cryptography.Games.Advantage\nTCSlib.Cryptography.Games.guessGame\tTCSlib.Cryptography.Games.Advantage\nTCSlib.Cryptography.acceptProb\tTCSlib.Cryptography.Foundations.Experiments\nTCSlib.Cryptography.distAdv\tTCSlib.Cryptography.Foundations.Experiments\nTCSlib.Cryptography.invProb\tTCSlib.Cryptography.Foundations.Experiments\nTCSlib.Cryptography.predProb\tTCSlib.Cryptography.Foundations.Experiments\nTCSlib.Cryptography.uexp\tTCSlib.Cryptography.Foundations.Probability\nTCSlib.Cryptography.uprob\tTCSlib.Cryptography.Foundations.Probability\nTCSlib.InformationTheory.FinDist.HasMinEntropy\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist._sizeOf_1\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.collision\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.map\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.mk._flat_ctor\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.probTrue\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.prod\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.FinDist.uniform\tTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.statDist\tTCSlib.InformationTheory.StatisticalDistance\n_private.TCSlib.Cryptography.Games.OracleComp.0.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1.splitter\tTCSlib.Cryptography.Games.OracleComp"
  let lines := if payload.isEmpty then [] else payload.splitOn "\n"
  unless lines.length == 50 do throwError "LAMP-HARNESS bad serialized count"
  let env ← Lean.getEnv
  let moduleNames := env.header.moduleNames
  let mut catalog : Std.HashMap String (Array Lean.Name) := {}
  for (n, _) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    unless (`TCSlib).isPrefixOf moduleNames[mi.toNat]! do continue
    catalog := catalog.insert n.toString (((catalog[n.toString]?).getD #[]).push n)
  let mut count : Nat := 0
  for row in lines do
    let [spelling, home] := row.splitOn "\t" | throwError "LAMP-HARNESS malformed row"
    let ns := (catalog[spelling]?).getD #[]
    unless ns.size == 1 do throwError "LAMP-HARNESS absent/ambiguous {spelling}"
    let n := ns[0]!
    let some mi := env.getModuleIdxFor? n | throwError "LAMP-HARNESS no home {spelling}"
    unless moduleNames[mi.toNat]!.toString == home do
      throwError "LAMP-HARNESS wrong home {spelling}"
    let some ci := env.find? n | throwError "LAMP-HARNESS no constant {spelling}"
    unless ci.isDefinition do throwError "LAMP-HARNESS not definition {spelling}"
    let after ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless after == .irreducible do throwError "LAMP-HARNESS unsealed {spelling}"
    Lean.logInfo m!"LAMP-SEAL-NAME\t{label}\tEOF\t{spelling}\t{home}"
    count := count + 1
  unless count == 50 do throwError "LAMP-HARNESS wrong verified count"
  Lean.logInfo m!"LAMP-SEAL-EOF\t{label}\t{count}"

