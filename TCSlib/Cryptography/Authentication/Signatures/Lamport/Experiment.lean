/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Statistics
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Authentication.Signatures.Lamport.AveragingExtra

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The typed Lamport reduction and its average success

## Main definitions

* `honestOutput` and `HonestSuccess`: the honest typed forgery and its acceptance/freshness test.
* `Favourable`: the sole query avoids the planted preimage and the forgery uses it.
* `RedSuccess`: a nonaborting planted simulation whose extracted block inverts its challenge.
* `honestProbability` and `redProbability`: the honest and independently challenged averages.

## Main results

* `favourable_mass_of_success`: favorable position mass is at least `1/(2n)` on successes.
* `diagonal_red_of_success_favourable`: favorable honest successes invert their table entry.
* `averaged_redProbability_ge`: uniform planted reduction success is at least `H/(2n)`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 137.1 and Theorem 137.2.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

open TCSlib.Cryptography.Games
open scoped Classical

-- Keep elaboration on the published probability readers.
run_cmd do
  for n in [``ProbComp.expect, ``ProbComp.sample, ``OracleComp.bind] do
    let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless status == .irreducible do
      let id := Lean.mkIdent n
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))

section TypedExperiment

variable {n ℓ : ℕ} {ρ : Type}
  (g : (Fin n → Bool) → Fin ℓ → Bool)
  (adv : ((Fin n × Bool) → Fin ℓ → Bool) → ρ →
    OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) (Fin (n + n * n) → Bool))

/-- Evaluate the forger on the honest public table with deterministic table signing. -/
def honestOutput (T : Table n) (r : ρ) : Fin (n + n * n) → Bool :=
  (adv (tablePublic g T) r).evalFn (fun _ m => tableSignature T m)

/-- The honest output is functional evaluation against the selected-preimage signing function. -/
theorem honestOutput_eq (T : Table n) (r : ρ) :
    honestOutput g adv T r =
      (adv (tablePublic g T) r).evalFn (fun _ m => tableSignature T m) := rfl

/-- An honest output succeeds when all its signature blocks verify and its message was
not the optional signing query [PS10, Definition 136.2]. -/
def HonestSuccess (T : Table n) (r : ρ) : Prop :=
  (∀ j, g (signatureBlock (splitBits (honestOutput g adv T r)).2 j) =
    g (T (j, (splitBits (honestOutput g adv T r)).1 j))) ∧
    firstQuery (adv (tablePublic g T) r) ≠ some (splitBits (honestOutput g adv T r)).1

/-- Honest success is coordinate verification together with inequality to the optional query. -/
theorem honestSuccess_iff (T : Table n) (r : ρ) :
    HonestSuccess g adv T r ↔
      (∀ j, g (signatureBlock (splitBits (honestOutput g adv T r)).2 j) =
        g (T (j, (splitBits (honestOutput g adv T r)).1 j))) ∧
      firstQuery (adv (tablePublic g T) r) ≠ some (splitBits (honestOutput g adv T r)).1 :=
  Iff.rfl

/-- A position-bit pair is favorable when its signing query is safe and its forged message
uses the planted bit [PS10, proof of Theorem 137.2]. -/
def Favourable (T : Table n) (r : ρ) (p : Fin n × Bool) : Prop :=
  Safe (adv (tablePublic g T) r) p.1 p.2 ∧
    (splitBits (honestOutput g adv T r)).1 p.1 = p.2

/-- Favorability is signing-query safety conjoined with the forged message's planted bit. -/
theorem favourable_iff (T : Table n) (r : ρ) (p : Fin n × Bool) :
    Favourable g adv T r p ↔ Safe (adv (tablePublic g T) r) p.1 p.2 ∧
      (splitBits (honestOutput g adv T r)).1 p.1 = p.2 := Iff.rfl

/-- The planted reduction succeeds if it ends without abort and its extracted signature
block is a preimage of the challenge [PS10, proof of Theorem 137.2]. -/
def RedSuccess (y : Fin ℓ → Bool) (T : Table n) (r : ρ) (p : Fin n × Bool) : Prop :=
  ∃ a, simulate (abortingImpl T p.1 p.2)
      (adv (plantedPublic g T p.1 p.2 y) r) false = .pure (a, false) ∧
    g (signatureBlock (splitBits a).2 p.1) = y

/-- Reduction success means a pure nonaborting simulation output whose selected block
maps to the challenge. -/
theorem redSuccess_iff (y : Fin ℓ → Bool) (T : Table n) (r : ρ) (p : Fin n × Bool) :
    RedSuccess g adv y T r p ↔
      ∃ a, simulate (abortingImpl T p.1 p.2)
          (adv (plantedPublic g T p.1 p.2 y) r) false = .pure (a, false) ∧
        g (signatureBlock (splitBits a).2 p.1) = y := Iff.rfl

/-- Replacing a table coordinate by its present value leaves the table unchanged. -/
theorem plantTable_self (T : Table n) (i : Fin n) (c : Bool) :
    plantTable T i c (T (i, c)) = T := by
  funext p
  rw [plantTable_eq]
  by_cases hp : p = (i, c)
  · rw [if_pos hp, hp]
  · rw [if_neg hp]

/-- Reduction success ignores the original table preimage at the planted position. -/
theorem redSuccess_plant_iff (y : Fin ℓ → Bool) (T : Table n) (r : ρ)
    (p : Fin n × Bool) (x : Fin n → Bool) :
    RedSuccess g adv y (plantTable T p.1 p.2 x) r p ↔ RedSuccess g adv y T r p := by
  rw [redSuccess_iff, redSuccess_iff, plantedPublic_plant, abortingImpl_plant]

/-- A favorable successful honest run is a successful planted reduction when challenged
with the image of its own selected table entry [PS10, proof of Theorem 137.2]. -/
theorem diagonal_red_of_success_favourable
    (hcost : ∀ Y r, (adv Y r).CostBoundedBy (fun _ => 1) 1)
    (T : Table n) (r : ρ) (p : Fin n × Bool)
    (hs : HonestSuccess g adv T r) (hq : Favourable g adv T r p) :
    RedSuccess g adv (g (T p)) T r p := by
  obtain ⟨hacc, hfresh⟩ := (honestSuccess_iff g adv T r).1 hs
  obtain ⟨hsafe, hbit⟩ := (favourable_iff g adv T r p).1 hq
  apply (redSuccess_iff g adv (g (T p)) T r p).2
  refine ⟨honestOutput g adv T r, ?_, ?_⟩
  · rw [plantedPublic_image, plantTable_self]
    have h := planted_coupling T p.1 p.2 (T p) (adv (tablePublic g T) r)
      (hcost _ r) hsafe
    rw [plantTable_self, ← honestOutput_eq g adv T r] at h
    exact h
  · have h := hacc p.1
    rw [hbit] at h
    exact h

/-- On every successful honest run, favorable position-bit mass is at least `1/(2n)`;
the no-query case has mass exactly `1/2` [PS10, proof of Theorem 137.2]. -/
theorem favourable_mass_of_success [Nonempty (Fin n)] (T : Table n) (r : ρ)
    (hs : HonestSuccess g adv T r) :
    1 / (2 * (n : ℝ)) ≤ ProbComp.expect (ProbComp.sample (Fin n × Bool))
      (fun p => if Favourable g adv T r p then (1 : ℝ) else 0) := by
  have h := LamportReduction.optionQuery_favourable_expect_ge
    (firstQuery (adv (tablePublic g T) r)) (splitBits (honestOutput g adv T r)).1
    ((honestSuccess_iff g adv T r).1 hs).2
  simp only [Fintype.card_fin] at h
  apply h.trans
  apply ProbComp.expect_mono
  intro p
  by_cases hp : Favourable g adv T r p
  · obtain ⟨hsafe, hbit⟩ := (favourable_iff g adv T r p).1 hp
    have hr : (∀ m, firstQuery (adv (tablePublic g T) r) = some m → m p.1 ≠ p.2) ∧
        (splitBits (honestOutput g adv T r)).1 p.1 = p.2 :=
      ⟨(safe_iff _ p.1 p.2).1 hsafe, hbit⟩
    simp only [if_pos hr, if_pos hp, le_refl]
  · have hr : ¬ ((∀ m, firstQuery (adv (tablePublic g T) r) = some m → m p.1 ≠ p.2) ∧
        (splitBits (honestOutput g adv T r)).1 p.1 = p.2) := by
      intro hh
      exact hp ((favourable_iff g adv T r p).2 ⟨(safe_iff _ p.1 p.2).2 hh.1, hh.2⟩)
    simp only [if_neg hr, if_neg hp, le_refl]

variable [Fintype ρ] [Nonempty ρ]

/-- Honest success probability averages over the complete key table and forger coins. -/
noncomputable def honestProbability : ℝ :=
  ProbComp.expect (ProbComp.sample (Table n)) fun T =>
    ProbComp.expect (ProbComp.sample ρ) fun r => if HonestSuccess g adv T r then 1 else 0

/-- Honest probability is the nested uniform expectation of the honest-success indicator. -/
theorem honestProbability_eq : honestProbability g adv =
    ProbComp.expect (ProbComp.sample (Table n)) (fun T =>
      ProbComp.expect (ProbComp.sample ρ) fun r => if HonestSuccess g adv T r then 1 else 0) := rfl

/-- The fixed-position reduction's success probability uses an independent challenge
preimage, a complete random table, and forger coins. -/
noncomputable def redProbability (p : Fin n × Bool) : ℝ :=
  ProbComp.expect (ProbComp.sample (Fin n → Bool)) fun x =>
    ProbComp.expect (ProbComp.sample (Table n)) fun T =>
      ProbComp.expect (ProbComp.sample ρ) fun r => if RedSuccess g adv (g x) T r p then 1 else 0

/-- Fixed-position reduction probability is the nested average of its nonaborting inversion
indicator over independent challenge, key-table and forger samples. -/
theorem redProbability_eq (p : Fin n × Bool) : redProbability g adv p =
    ProbComp.expect (ProbComp.sample (Fin n → Bool)) (fun x =>
      ProbComp.expect (ProbComp.sample (Table n)) fun T =>
        ProbComp.expect (ProbComp.sample ρ) fun r => if RedSuccess g adv (g x) T r p then 1 else 0) :=
  rfl

/-- A uniform position-bit planted reduction succeeds with probability at least the honest
forgery probability divided by `2n` [PS10, proof of Theorem 137.2].

**Proof sketch.** Favorable pairs occupy at least `1/(2n)` of every successful honest run.
On those pairs the planted simulation is safe and its extracted signature block inverts
the image of the corresponding honest preimage. The reduction ignores that preimage,
so coordinate resampling makes the challenge independent while preserving the average. -/
theorem averaged_redProbability_ge [Nonempty (Fin n)]
    (hcost : ∀ Y r, (adv Y r).CostBoundedBy (fun _ => 1) 1) :
    honestProbability g adv / (2 * (n : ℝ)) ≤
      ProbComp.expect (ProbComp.sample (Fin n × Bool)) (redProbability g adv) := by
  classical
  have h := coordinate_reduction_bound
    (HonestSuccess g adv) (Favourable g adv)
    (fun x T r p => RedSuccess g adv (g x) T r p) (1 / (2 * (n : ℝ)))
    (favourable_mass_of_success g adv)
    (diagonal_red_of_success_favourable g adv hcost)
    (fun x x' T r p => by
      rw [← plantTable_update T p.1 p.2 x']
      exact redSuccess_plant_iff g adv (g x) T r p x')
  simpa only [honestProbability_eq, redProbability_eq, one_div_mul_eq_div] using h

/-- Some fixed position, while its planted bit remains fair, has reduction probability at
least `H/(2n)` [PS10, proof of Theorem 137.2]. This is the position supplied as advice. -/
theorem exists_best_position [Nonempty (Fin n)]
    (hcost : ∀ Y r, (adv Y r).CostBoundedBy (fun _ => 1) 1) :
    ∃ i : Fin n, honestProbability g adv / (2 * (n : ℝ)) ≤
      ProbComp.expect (ProbComp.sample Bool) (fun c => redProbability g adv (i, c)) := by
  obtain ⟨i, hi⟩ := LamportReduction.exists_position_fairBit_expect_ge
    (fun i : Fin n => fun c : Bool => redProbability g adv (i, c))
  exact ⟨i, (averaged_redProbability_ge g adv hcost).trans hi⟩

end TypedExperiment

end TCSlib.Cryptography.Authentication.LamportFill
