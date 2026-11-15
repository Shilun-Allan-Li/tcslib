/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.BoundedMetadata
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalAdvice
import TCSlib.Cryptography.Composability.SequentialZK.ReductionAdvantage
import TCSlib.Cryptography.Composability.SequentialZK.ContinuationProbability
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One negligible bound for all bounded phase continuations

## Main definitions

This module introduces no definitions or computational hosts.

## Main results

* `exists_negligible_phase_bound`: the wrapped original simulator gives one negligible
  bound for every bounded phase metadata tuple, with no witness in the reduction advice.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1.
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity Turing

/-- Let `π,R,V,S` have a uniform simulator satisfying the computational comparison for
`π` against `phaseVerifier V`, for every auxiliary polynomial and nonuniform distinguisher.
For fixed `Lz,D,Q,B`, one negligible `ε` bounds `phaseGap` by `|ε(|x|)|` for every witness,
auxiliary word `|z|≤Lz(|x|)`, verifier tape of its exact prescribed length, phase `j<Q(|x|)`,
and prefix with encoding length at most `Q(|x|)*π.rounds(|x|)*(2*B(|x|)+2)`.
No prover bound, witness bound or reachability premise is required for this comparison.
[PS10, Theorem 175.1, common negligible phase bound for sequential zero knowledge].

**Proof sketch.**
Use a syntactic polynomial for the complete encoded-prefix envelope.
Pack the input, auxiliary word, verifier tape, phase and raw prefix into finite metadata.
These metadata types remain nonempty at every parameter, including zero phases.
The existing advantage bound by one bounds every metadata and witness gap.
Validity is a proof-only relation: the witness is valid, the prefix is canonical, and the
phase lies strictly below the repetition count. No machine tests this relation.
Apply the published finite advice selector before requesting any negligible bound.
For any selected metadata function, its public length reader gives a polynomial advice bound.
The uniform continuation sampler and ordinary advice closure build one nonuniform reduction.
Canonical-prefix validity identifies its packed advice with input paired with phase auxiliary.
The public second-projection length bound therefore bounds that auxiliary word.
Apply the given original simulator comparison to this reduction and auxiliary polynomial.
The exact typed reduction advantage reader identifies the selected local phase gap.
The finite selector propagates this negligible bound to every valid metadata tuple.
Finally the public exact-cover reader represents each supplied typed prefix and bounded tuple.
The decoder's public encoding equation recovers that prefix without changing any bits.
Substitution yields the claimed common bound for all witnesses and all fixed verifier tapes. -/
theorem exists_negligible_phase_bound (π : Protocol) (R : List Bool → List Bool → Prop)
    (V : Strategy) (S : NUPPT) (hS : S.Uniform)
    (hclose : ∀ (Lz' : PolyExpr) (Red : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ x y aux, R x y → aux.length ≤ Lz'.eval x.length →
        distAdv (fun r => ((π.withV (phaseVerifier V)).viewV x y aux r).encode)
          (S.simulate x aux) (Red.distinguisherL x.length) ≤ ε x.length)
    (Lz : PolyExpr) (D : NUPPT) (Q B : PolyExpr) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ x y z rV j pre, R x y →
      z.length ≤ Lz.eval x.length → rV.length = V.coinLen x.length → j < Q.eval x.length →
      (Strategy.encodeMsgs pre).length ≤
        Q.eval x.length * π.rounds.eval x.length * (2 * B.eval x.length + 2) →
      phaseGap π V S B Q x y z rV (D.distinguisherL x.length) j pre ≤ |ε x.length| := by
  classical
  -- Fix finite metadata bounds and the common polynomial advice envelope.
  let H : PolyExpr := .mul (.mul Q π.rounds) (.add (.mul (.const 2) B) (.const 2))
  let b : PolyExpr := .add (.add (.add (.add (.add (.mul (.const 2) .var)
    (.mul (.const 2) Lz)) (.mul (.const 2) V.coins)) (.mul (.const 2) Q)) H) (.const 8)
  have hH (n : ℕ) : H.eval n = Q.eval n * π.rounds.eval n * (2 * B.eval n + 2) := by
    simp only [H, PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
  have hb (n : ℕ) : b.eval n =
      2 * n + 2 * Lz.eval n + 2 * V.coinLen n + 2 * Q.eval n + H.eval n + 8 := by
    simp only [b, PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const,
      PolyExpr.eval_var, Strategy.coinLen_eq]
  let A (n : ℕ) := PhaseMetadata n (Lz.eval n) (V.coinLen n) (Q.eval n) (H.eval n)
  let gap (n : ℕ) (m : A n) (y : List Bool) : ℝ :=
    phaseGap π V S B Q (List.ofFn m.1) y (List.ofFn m.2.1.2) (List.ofFn m.2.2.1)
      (D.distinguisherL (List.ofFn m.1).length) m.2.2.2.1
      (BinArith.decWords (List.ofFn m.2.2.2.2.2))
  let valid (n : ℕ) (m : A n) (y : List Bool) : Prop :=
    R (List.ofFn m.1) y ∧
      Strategy.encodeMsgs (BinArith.decWords (List.ofFn m.2.2.2.2.2)) =
        List.ofFn m.2.2.2.2.2 ∧ (m.2.2.2.1 : ℕ) < Q.eval n
  have hgap (n : ℕ) (m : A n) (y : List Bool) : gap n m y ≤ 1 := by
    dsimp only [gap]
    rw [phaseGap_eq]
    exact ColZK.distAdv_le_one _ _ _
  -- The selector sees a bounded gap and a proof-only validity predicate.
  have hchoice (choice : (n : ℕ) → A n) : ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n y, valid n (choice n) y → gap n (choice n) y ≤ ε n := by
    let X (n : ℕ) := List.ofFn (choice n).1
    let Z (n : ℕ) := List.ofFn (choice n).2.1.2
    let RV (n : ℕ) := List.ofFn (choice n).2.2.1
    let J (n : ℕ) : ℕ := (choice n).2.2.2.1
    let PW (n : ℕ) := List.ofFn (choice n).2.2.2.2.2
    -- One metadata choice gives ordinary bounded advice, independent of the witness.
    have hdata (n : ℕ) : (reductionData (X n) (Z n) (RV n) (J n) (PW n)).length ≤
        b.eval n := by
      rw [hb]
      simpa only [PhaseMetadata.toData_eq, X, Z, RV, J, PW] using
        (choice n).toData_length_le
    obtain ⟨Red, hcoins, hrun⟩ := exists_phaseReduction S hS D π.rounds B Q
      π.verifierFirst X Z RV J PW b hdata
    obtain ⟨ε, hε, hbound⟩ := hclose b Red
    refine ⟨ε, hε, ?_⟩
    intro n y hy
    have hx : (X n).length = n := List.length_ofFn
    have hcanon : Strategy.encodeMsgs (BinArith.decWords (PW n)) = PW n := hy.2.1
    have hpack : reductionData (X n) (Z n) (RV n) (J n) (PW n) =
        pairEncode (X n) (phaseAux (Z n) (RV n) (J n) (BinArith.decWords (PW n))) := by
      exact (congrArg (reductionData (X n) (Z n) (RV n) (J n)) hcanon.symm).trans
        (reductionData_encodeMsgs (X n) (Z n) (RV n) (J n) (BinArith.decWords (PW n)))
    -- Canonical raw advice is input paired with auxiliary; projection bounds its length.
    have haux : (phaseAux (Z n) (RV n) (J n) (BinArith.decWords (PW n))).length ≤
        b.eval (X n).length := by
      rw [hx]
      calc
        _ = (pairSndD (reductionData (X n) (Z n) (RV n) (J n) (PW n))).length := by
          rw [hpack, pairSndD_pairEncode]
        _ ≤ (reductionData (X n) (Z n) (RV n) (J n) (PW n)).length :=
          length_pairSndD_le _
        _ ≤ b.eval n := hdata n
    -- The selected advised reduction is exactly the typed local continuation experiment.
    have hlocal := hbound (X n) y
      (phaseAux (Z n) (RV n) (J n) (BinArith.decWords (PW n))) hy.1 haux
    have hrunAt : ∀ raw r, Red.runAtL (X n).length raw r =
        D.runAtL (X n).length
          (phaseContinuation S π.rounds B Q π.verifierFirst (X n) (Z n) (RV n)
            (J n) (BinArith.decWords (PW n)) raw
            (r.take ((PolyExpr.mul Q S.coins).eval (X n).length)))
          (r.drop ((PolyExpr.mul Q S.coins).eval (X n).length)) := by
      simpa only [hx] using hrun n
    have heq := distAdv_phaseReduction S D Red π.rounds B Q π.verifierFirst (X n).length
      (X n) (Z n) (RV n) (J n) (BinArith.decWords (PW n)) hcoins hrunAt
      (fun r => ((π.withV (phaseVerifier V)).viewV (X n) y
        (phaseAux (Z n) (RV n) (J n) (BinArith.decWords (PW n))) r).encode)
      (S.simulate (X n) (phaseAux (Z n) (RV n) (J n) (BinArith.decWords (PW n))))
    have hgapEq : gap n (choice n) y =
        distAdv (fun r => ((π.withV (phaseVerifier V)).viewV (X n) y
          (phaseAux (Z n) (RV n) (J n) (BinArith.decWords (PW n))) r).encode)
          (S.simulate (X n) (phaseAux (Z n) (RV n) (J n) (BinArith.decWords (PW n))))
          (Red.distinguisherL (X n).length) := by
      dsimp only [gap]
      rw [phaseGap_eq]
      simpa only [X, Z, RV, J, PW] using heq.symm
    have hscalar : gap n (choice n) y ≤ ε (X n).length := by
      rw [hgapEq]
      exact hlocal
    simpa only [hx] using hscalar
  -- The public selector chooses metadata before epsilon and then bounds every valid tuple.
  obtain ⟨ε, hε, hall⟩ := exists_uniform_negligible_bound gap valid hgap hchoice
  refine ⟨ε, hε, ?_⟩
  -- Exact finite coverage recovers every bounded caller-supplied prefix and metadata tuple.
  intro x y z rV j pre hxy hz hrV hj hpre
  obtain ⟨m, hx, hz', hrV', hj', hpre'⟩ := PhaseMetadata.cover (h := H.eval x.length) x z rV j
    (Strategy.encodeMsgs pre) rfl hz hrV hj.le (by simpa only [hH] using hpre)
  have hdecode : BinArith.decWords (List.ofFn m.2.2.2.2.2) = pre := by
    rw [hpre', encodeMsgs_eq_encWords, BinArith.decWords_encWords]
  have hvalid : valid x.length m y := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hx] using hxy
    · rw [hdecode, hpre']
    · simpa only [hj'] using hj
  have hcovered : gap x.length m y =
      phaseGap π V S B Q x y z rV (D.distinguisherL x.length) j pre := by
    dsimp only [gap]
    rw [hz', hrV', hj', hdecode]
    exact congrArg (fun u : List Bool =>
      phaseGap π V S B Q u y z rV (D.distinguisherL u.length) j pre) hx
  rw [← hcovered]
  exact hall x.length m y hvalid

end TCSlib.Cryptography.SequentialZK
