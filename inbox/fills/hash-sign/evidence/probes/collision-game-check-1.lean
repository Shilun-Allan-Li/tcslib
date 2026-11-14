/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CollisionHandler
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The collision probability in the hash-and-sign reduction

## Main definitions

* `HashSignFill.CollisionCase`: the final message is fresh and has the same hash as some
  logged query.

## Main results

* `HashSignFill.exists_collisionGame_bound`: the common transcript's collision case is
  bounded by the collision probability of one machine.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 144.1, collision-finding case.
-/

namespace TCSlib.Cryptography.Authentication.HashSignFill

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- The collision case of a common transcript: its final message is distinct from every
logged query, and some logged query has its hash [PS10, Theorem 144.1]. -/
def CollisionCase (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n)))) : Prop :=
  (∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1) ∧
    ∃ e ∈ res.2.2, H.hash n i e.2.1 = H.hash n i (splitBits res.1).1

/-- The collision case holds exactly when the final message is fresh and a logged query
has the same hash as that message. -/
theorem collisionCase_iff (H : CRH) (S : SignatureScheme) (n : ℕ) (i : List Bool)
    (res : (Fin (H.domLen.eval n + S.sigLen.eval n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => H.domLen.eval n)
        (fun _ => S.sigLen.eval n)))) :
    CollisionCase H S n i res ↔
      (∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1) ∧
        ∃ e ∈ res.2.2, H.hash n i e.2.1 = H.hash n i (splitBits res.1).1 := Iff.rfl

/-- A machine's collision probability bounds the collision case of the common transcript,
averaged over the original keys, hash index, adversary tape and signing tape
[PS10, Theorem 144.1].

**Proof sketch.** T1 constructs a machine with the same deterministic transcript on each
choice of seed and adversary tape. In the collision case its output satisfies the exact
CRH collision predicate. Average this pointwise indicator inequality. The seed equivalence
concatenates the original generator and signer tapes; the T1 coin equivalence then turns
the seed and adversary tapes into uniform collision-finder coins. Independent samples may
be exchanged, so the resulting average is exactly the CRH game's acceptance probability. -/
theorem exists_collisionGame_bound (H : CRH) (S : SignatureScheme) (A : NUPPT)
    (hdom : ∀ n i x, H.inDom n i x = true) :
    ∃ B : NUPPT, ∀ n,
      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
        ProbComp.expect (ProbComp.sample (H.gen.Coins n)) (fun ri =>
          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
            ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
              ProbComp.prob (transcript H S A n (pairFstD (S.gen.runAt n [] rg))
                (pairSndD (S.gen.runAt n [] rg)) (H.gen.runAt n [] ri) rs rA)
                (CollisionCase H S n (H.gen.runAt n [] ri)))))) ≤
        accept (H.collisionGame B n) := by
  classical
  obtain ⟨B, hB⟩ := exists_collisionMachine_transcript H S A
  refine ⟨B, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  let seed : S.gen.Coins n × S.sign.Coins n ≃
      (Fin ((collisionHandler H S).seedLen.eval n) → Bool) :=
    EnsembleLemmas.seedEquiv (A := S.gen) (B := S.sign) (collisionHandler_seedLen H S) n
  let win : List Bool → B.Coins n → Prop := fun i r =>
    let xx := splitBits (padFin (H.domLen.eval n + H.domLen.eval n) (B.runAt n i r))
    H.inDom n i xx.1 = true ∧ H.inDom n i xx.2 = true ∧ xx.1 ≠ xx.2 ∧
      H.hash n i xx.1 = H.hash n i xx.2
  have hpoint (rg : S.gen.Coins n) (rs : S.sign.Coins n) (rA : A.Coins n) (i : List Bool) :
      ProbComp.prob (transcript H S A n (pairFstD (S.gen.runAt n [] rg))
        (pairSndD (S.gen.runAt n [] rg)) i rs rA) (CollisionCase H S n i) ≤
        if win i (φ (seed (rg, rs), rA)) then (1 : ℝ) else 0 := by
    obtain ⟨a, s, L, ht, hinv, hrun⟩ := hφ i rg rs (seed (rg, rs)) rA
      (EnsembleLemmas.seedEquiv_ofFn (collisionHandler_seedLen H S) n (rg, rs))
    rw [ht, ProbComp.prob_pure]
    by_cases hcase : CollisionCase H S n i (a, ((), L))
    · have hclauses := (collisionCase_iff H S n i (a, ((), L))).mp hcase
      have hw : win i (φ (seed (rg, rs), rA)) := by
        dsimp only [win]
        rw [hrun]
        exact collisionHandler_collision H S hdom n (pairSndD (S.gen.runAt n [] rg)) i rs
          (seed (rg, rs)) a s L hinv hclauses.1 hclauses.2
      simp only [hcase, hw, if_true]
    · simp only [hcase, if_false]
      split_ifs <;> norm_num
  have hcoins (i : List Bool) :
      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
        ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
            if win i (φ (seed (rg, rs), rA)) then (1 : ℝ) else 0))) =
        ProbComp.expect (ProbComp.sample (B.Coins n)) (fun r =>
          if win i r then (1 : ℝ) else 0) := by
    calc
      _ = ProbComp.expect (ProbComp.sample (S.gen.Coins n × S.sign.Coins n)) (fun p =>
          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
            if win i (φ (seed p, rA)) then (1 : ℝ) else 0)) := by
        simpa only [ProbComp.expect_bind, ProbComp.expect_pure] using
          Bridge.expect_sample_pair (fun p : S.gen.Coins n × S.sign.Coins n =>
            ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
              if win i (φ (seed p, rA)) then (1 : ℝ) else 0))
      _ = ProbComp.expect
          (ProbComp.sample (Fin ((collisionHandler H S).seedLen.eval n) → Bool)) (fun ω =>
          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
            if win i (φ (ω, rA)) then (1 : ℝ) else 0)) :=
        ProbComp.expect_sample_equiv seed _
      _ = ProbComp.expect (ProbComp.sample
          ((Fin ((collisionHandler H S).seedLen.eval n) → Bool) × A.Coins n)) (fun p =>
          if win i (φ p) then (1 : ℝ) else 0) := by
        simpa only [ProbComp.expect_bind, ProbComp.expect_pure] using
          Bridge.expect_sample_pair (fun p :
            (Fin ((collisionHandler H S).seedLen.eval n) → Bool) × A.Coins n =>
            if win i (φ p) then (1 : ℝ) else 0)
      _ = _ := ProbComp.expect_sample_equiv φ _
  calc
    _ ≤ ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
        ProbComp.expect (ProbComp.sample (H.gen.Coins n)) (fun ri =>
          ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
            ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
              if win (H.gen.runAt n [] ri) (φ (seed (rg, rs), rA)) then (1 : ℝ) else 0)))) := by
      apply ProbComp.expect_mono
      intro rg
      apply ProbComp.expect_mono
      intro ri
      apply ProbComp.expect_mono
      intro rA
      exact ProbComp.expect_mono _ (fun rs => hpoint rg rs rA (H.gen.runAt n [] ri))
    _ = ProbComp.expect (ProbComp.sample (H.gen.Coins n)) (fun ri =>
        ProbComp.expect (ProbComp.sample (S.gen.Coins n)) (fun rg =>
          ProbComp.expect (ProbComp.sample (S.sign.Coins n)) (fun rs =>
            ProbComp.expect (ProbComp.sample (A.Coins n)) (fun rA =>
              if win (H.gen.runAt n [] ri) (φ (seed (rg, rs), rA)) then (1 : ℝ) else 0)))) := by
      rw [ProbComp.expect_sample_comm]
      congr 1
      funext ri
      congr 1
      funext rg
      exact ProbComp.expect_sample_comm _
    _ = ProbComp.expect (ProbComp.sample (H.gen.Coins n)) (fun ri =>
        ProbComp.expect (ProbComp.sample (B.Coins n)) (fun r =>
          if win (H.gen.runAt n [] ri) r then (1 : ℝ) else 0)) := by
      congr 1
      funext ri
      exact hcoins (H.gen.runAt n [] ri)
    _ = accept (H.collisionGame B n) := by
      simp only [accept_eq, CRH.collisionGame_eq, ProbComp.prob_bind, ProbComp.prob_pure,
        decide_eq_true_eq]
      rfl

end TCSlib.Cryptography.Authentication.HashSignFill
