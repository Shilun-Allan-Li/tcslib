import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Schnorr Identification Protocol

## Main results

- `schnorr_completeness`: honest transcripts always satisfy the verifier equation
- `schnorr_soundness`: two accepting transcripts with distinct challenges allow witness extraction
- `schnorr_hvzk`: simulator transcripts equal honest transcripts via bijective reindexing

## References

- Original formalization by Esha Garg
-/

namespace Schnorr

variable {G : Type*} [CommGroup G]
variable {q : ℕ} [Fact q.Prime]
variable (g : G)

/-- A prime is nonzero, so `Fact q.Prime` gives `NeZero q` automatically.
Registered as an instance so that `ZMod.val_add`, `ZMod.val_mul`, and the
`ZMod.natCast_*` cast lemmas resolve their `[NeZero q]` arguments without
a manual `haveI` in each proof. -/
instance neZero_of_factPrime : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

/-- A Schnorr transcript `(a, c, s)`: commitment in `G`, challenge and
response in `ZMod q`. -/
abbrev Transcript (G : Type*) (q : ℕ) := G × ZMod q × ZMod q

/-- Prover's first message: commitment `a := g ^ r` for randomness `r`. -/
def commit (r : ZMod q) : G := g ^ r.val

/-- Prover's second message: response `s := r + c·w` for witness `w`,
randomness `r`, challenge `c`. -/
def respond (w r c : ZMod q) : ZMod q := r + c * w

/-- Verifier's accept predicate: `g ^ s = a · pk ^ c`. -/
def Verify (pk a : G) (c s : ZMod q) : Prop :=
  g ^ s.val = a * pk ^ c.val

/-- Full honest transcript: `(commit g r, c, respond w r c)`. -/
def honest (w r c : ZMod q) : Transcript G q :=
  (commit g r, c, respond w r c)

/-- Simulator transcript for challenge `c` and fresh response `s`,
setting `a := g^s · (pk^c)⁻¹`. Does not use the witness. -/
def simulate (pk : G) (c s : ZMod q) : Transcript G q :=
  (g ^ s.val * (pk ^ c.val)⁻¹, c, s)

/-- Two-transcript witness extractor: `(s₁ - s₂) / (c₁ - c₂)` in `ZMod q`. -/
def extract (c₁ c₂ s₁ s₂ : ZMod q) : ZMod q :=
  ((s₁ - s₂) / (c₁ - c₂) : ZMod q)

/-- **Completeness**: for any witness `w`, randomness `r`, and challenge `c`
in `ZMod q`, with generator `g` of order `q`, the honest transcript
`(g^r, c, r + c·w)` satisfies the verifier equation
`g ^ (r + c·w).val = g^r.val * (g^w.val)^c.val`. -/
theorem schnorr_completeness
    (hg : orderOf g = q) (w r c : ZMod q) :
    Verify g (g ^ w.val) (commit g r) c (respond w r c) := by
  simp only [Verify, commit, respond]
  rw [← pow_mul, ← pow_add, pow_eq_pow_iff_modEq, hg]
  have h1 : (r + c * w).val ≡ r.val + (c * w).val [MOD q] := by
    rw [ZMod.val_add]
    exact Nat.mod_modEq _ _
  have h2 : (c * w).val ≡ w.val * c.val [MOD q] := by
    rw [ZMod.val_mul, mul_comm]
    exact Nat.mod_modEq _ _
  exact h1.trans (h2.add_left _)

/-- **Special soundness**: given a generator `g` of order `q` and two
accepting transcripts `(a, c₁, s₁)` and `(a, c₂, s₂)` for public key
`pk = g^w` that share the commitment `a` but use distinct challenges
`c₁ ≠ c₂`, the extractor recovers the witness:
`(s₁ - s₂) / (c₁ - c₂) = w`  in  `ZMod q`. -/
theorem schnorr_soundness
    (hg : orderOf g = q)
    (w : ZMod q) (a : G) (c₁ c₂ s₁ s₂ : ZMod q) (hne : c₁ ≠ c₂)
    (h₁ : Verify g (g ^ w.val) a c₁ s₁)
    (h₂ : Verify g (g ^ w.val) a c₂ s₂) :
    extract c₁ c₂ s₁ s₂ = w := by
  simp only [Verify] at h₁ h₂
  have key1 : g ^ s₁.val * (g ^ w.val) ^ c₂.val
      = g ^ s₂.val * (g ^ w.val) ^ c₁.val := by
    rw [h₁, h₂, mul_right_comm]
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
      pow_eq_pow_iff_modEq, hg] at key1
  have hZ : s₁ + w * c₂ = s₂ + w * c₁ := by
    simpa using (ZMod.natCast_eq_natCast_iff _ _ q).mpr key1
  have hsub : s₁ - s₂ = w * (c₁ - c₂) := by linear_combination hZ
  have hc_ne : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
  rw [extract, div_eq_iff hc_ne]
  exact hsub

/-- Reindexing bijection on `ZMod q`: `r ↦ r + c·w`, inverse `s ↦ s - c·w`. -/
def reindex (w c : ZMod q) : ZMod q ≃ ZMod q where
  toFun r := r + c * w
  invFun s := s - c * w
  left_inv := by intro r; ring
  right_inv := by intro s; ring

/-- **HVZK (pointwise)**: for every fixed witness `w` and challenge `c`,
with generator `g` of order `q`, the honest transcript function
`r ↦ honest g w r c` and the simulator transcript function
`s ↦ simulate g (g^w) c s` are equal as functions `ZMod q → Transcript G q`
after the bijective reindexing `s = r + c·w` (i.e. `reindex w c`). -/
theorem schnorr_hvzk
    (hg : orderOf g = q) (w c : ZMod q) :
    (fun r => honest g w r c) =
    (fun r => simulate g (g ^ w.val) c (reindex w c r)) := by
  funext r
  simp only [honest, simulate, commit, respond, reindex]
  refine Prod.ext ?_ rfl
  rw [eq_mul_inv_iff_mul_eq]
  exact (schnorr_completeness g hg w r c).symm

end Schnorr
