/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.LPN
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.PRG
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Stretch

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Explicit JLS security inequalities and their corollaries

## Main definitions

* `Params.Realizable`: the conjunction of the shared realiser obligations.

## Main results

* `lemma42`, `prop41`: explicit every-realiser advantage bounds.
* `theorem41` and its negligible/subexponential existence corollaries on Raw.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026, §§2-4.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8 (non-uniform PPT adversaries).
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

open Complexity
open TCSlib.Cryptography.Games

namespace Params

/-- Realisability supplies a NUPPT for each explicit reduction and advice family
[JLS26, Proposition 4.1, pp. 18-19]. Dv14 leaves this Phase B obligation as a
hypothesis; targets discharge it through the shared preTarget theorem. Dv16:
the shared RealizesOn constrains only encoded challenges and layout-length coins,
which weakens the predicate and strengthens every-realiser security inequalities. -/
def Realizable (P : Params) (π : PrimeSchedule) : Prop :=
  P.LPNRealizable π ∧ P.PRGRealizable π

/-- Realisability is the conjunction of the two shared-realiser propositions; glue. -/
theorem realizable_iff (P : Params) (π : PrimeSchedule) :
    P.Realizable π ↔ P.LPNRealizable π ∧ P.PRGRealizable π := Iff.rfl

end Params

/-- The initial real-tail distribution and final uniform-tail distribution differ by at
most κ LPN advantages plus one Boolean PRG advantage [JLS26, Lemma 4.2, p. 19].
Dv8 includes independent buckets; Dv12 hardwires averaging choices; Dv14 states the
bound for every realising NUPPT, with no machine construction.

**Proof sketch.** Choose the largest gap in the real-tail chain, hardwire its other draws
in LPN advice at every inverse-indexed dimension, and apply the every-realiser hop lemma.
Use the PRG hop on the all-uniform public vectors, then the existing hybrid inequality. -/
theorem lemma42 (P : Params) (π : PrimeSchedule) (A : NUPPT) :
    ∃ (ωL : ∀ L, P.LPNAdvice π L) (ωG : ∀ N, P.PRGAdvice π N),
      ∀ BL BG : NUPPT,
        BL.RealizesOn (P.lpnEnc π) (A.coins.subst .var)
          (fun L x r => P.lpnRed π A L (ωL L) x r) →
        BG.RealizesOn P.prgEnc (A.coins.subst .var)
          (fun N x r => P.prgRed π A N (ωG N) x r) →
        ∀ κ, advantage (P.chainGame A true 0 κ (π κ))
          (P.chainGame A false κ κ (π κ)) ≤
            (κ : ℝ) * (P.lpnFamily_raw π).adv BL (P.ℓ κ) + P.G.adv BG (P.n κ) := sorry

/-- The raw sPRG advantage is at most 2κ LPN advantages, one PRG advantage and twice
the exact error probability [JLS26, Proposition 4.1, pp. 18-19]. Dv1 fixes the schedule;
Dv9 quantifies every prime schedule; Dv12 hardwires averaging choices; Dv18 uses Raw.
Dv16: RealizesOn constrains only encoded challenges and layout-length coins, so its
weaker predicate makes this every-realiser inequality stronger.

**Proof sketch.** Bound H0-H1 and H2-H3 by the error event. Connect H1 to H2 by the
real-tail LPN chain, the PRG hop, and the reversed uniform-tail LPN chain. At each κ
choose the largest of the 2κ LPN gaps and hardwire the remaining draws. The shared
realiser readers identify every realiser's verdict, and the existing hybrid inequalities
sum the gaps. At κ=0 only the PRG hop and the explicit error slack remain. -/
theorem prop41 (P : Params) (π : PrimeSchedule) (A : NUPPT) :
    ∃ (ωL : ∀ L, P.LPNAdvice π L) (ωG : ∀ N, P.PRGAdvice π N),
      ∀ BL BG : NUPPT,
        BL.RealizesOn (P.lpnEnc π) (A.coins.subst .var)
          (fun L x r => P.lpnRed π A L (ωL L) x r) →
        BG.RealizesOn P.prgEnc (A.coins.subst .var)
          (fun N x r => P.prgRed π A N (ωG N) x r) →
        ∀ κ, (jlsSPRG_raw P π).adv A κ ≤
          2 * (κ : ℝ) * (P.lpnFamily_raw π).adv BL (P.ℓ κ) +
            P.G.adv BG (P.n κ) + 2 * P.errProb κ (π κ) := sorry

/-- Under realisability and the two assumptions, the raw construction is secure
[JLS26, Theorem 4.1, p. 11]. Dv3 uses the construction's own LPN family; Dv13 uses
NUPPT adversaries; Dv14 retains realisability as the Phase B obligation, and Dv18 uses Raw.

**Proof sketch.** Instantiate the advice from prop41 and the realisers from Realizable.
Reindex negligible LPN and PRG advantages along ℓ≥κ and n≥κ. Multiply by the polynomial
2κ, add the Claim 4.2 slack, and use the shared negligibility closure lemmas. -/
theorem jls_secure (P : Params) (π : PrimeSchedule) {cLoc : ℕ}
    (hLoc : P.R.HasLocality cLoc) (hR : P.Realizable π)
    (hG : P.G.Secure) (hLPN : (P.lpnFamily_raw π).Assumption) :
    (jlsSPRG_raw P π).Secure := sorry

/-- The raw advantage has explicit subexponential exponent
min(E*cL,min(E*D*cG,1))/2 [JLS26, Theorem 4.1, p. 11]. Dv13 uses the shared
SubexpSmall API against NUPPT; Dv14 assumes realisability; Dv18 uses Raw.

**Proof sketch.** Reindex the LPN term by κ^E and PRG term by κ^(E*D). Use the shared
polynomial-factor and constant-factor closure lemmas at an intermediate exponent below
the common minimum. Claim 4.2 controls the error term by 2^(-κ). Two applications of
sum closure yield half the minimum, then prop41 gives domination of the advantage. -/
theorem jls_subexpSmall (P : Params) (π : PrimeSchedule) {cLoc : ℕ}
    (hLoc : P.R.HasLocality cLoc) (hR : P.Realizable π) {cL cG : ℝ}
    (hcL : 0 < cL) (hcG : 0 < cG)
    (hG : ∀ B : NUPPT, SubexpSmall cG (P.G.adv B))
    (hLPN : ∀ B : NUPPT, SubexpSmall cL ((P.lpnFamily_raw π).adv B)) (A : NUPPT) :
    SubexpSmall (min ((P.E : ℝ) * cL) (min ((P.E : ℝ) * P.D * cG) 1) / 2)
      ((jlsSPRG_raw P π).adv A) := sorry

/-- Subexponential hardness of both assumptions gives subexponential raw sPRG security
[JLS26, Theorem 4.1, p. 11]. Dv13 quantifies a common exponent before every adversary;
Dv14 assumes the Phase B realisability obligation; Dv18 uses Raw.

**Proof sketch.** Read the two shared SubexpHard witnesses, use jls_subexpSmall, and
observe that its positive exponent depends only on the assumption exponents and P. -/
theorem jls_subexpSecure (P : Params) (π : PrimeSchedule) {cLoc : ℕ}
    (hLoc : P.R.HasLocality cLoc) (hR : P.Realizable π)
    (hG : SubexpHard P.G.adv) (hLPN : SubexpHard (P.lpnFamily_raw π).adv) :
    SubexpHard (jlsSPRG_raw P π).adv := sorry

/-- The raw construction is secure, has public degree d and private degree two, and
polynomial stretch [JLS26, Theorem 4.1, p. 11]. Dv1 fixes a sufficiently large schedule;
Dv3 uses its own LPN family; Dv6 uses composite bidegree; Dv9 allows every prime schedule;
Dv10 follows p. 17's degree d; Dv14 assumes realisability; Dv18 uses Raw.
SP-W1 restricts δ to rational data, coerced to real values in the stretch threshold.

**Proof sketch.** Combine raw security, the G4 correctness/degree theorem, and Claim 4.1. -/
theorem theorem41 (P : Params) (π : PrimeSchedule) {cLoc : ℕ} {τ : ℝ}
    (hLoc : P.R.HasLocality cLoc) (hτ : 1 < τ) (hs : P.G.HasStretch τ)
    (hE : E0 P.d (P.δ : ℝ) τ ≤ P.E) (hR : P.Realizable π)
    (hG : P.G.Secure) (hLPN : (P.lpnFamily_raw π).Assumption) :
    (jlsSPRG_raw P π).Secure ∧ (jlsSPRG_raw P π).HasComplexity P.d 2 ∧
      (jlsSPRG_raw P π).HasPolyStretch := sorry

/-- The raw construction has the same complexity/stretch and subexponential security
[JLS26, Theorem 4.1, p. 11]. Dv13 means advantage against NUPPT, Dv14 assumes
realisability, and Dv18 leaves the primitive assembly to the targets.

**Proof sketch.** Combine jls_subexpSecure, G4 correctness/degree, and Claim 4.1. -/
theorem theorem41_subexp (P : Params) (π : PrimeSchedule) {cLoc : ℕ} {τ : ℝ}
    (hLoc : P.R.HasLocality cLoc) (hτ : 1 < τ) (hs : P.G.HasStretch τ)
    (hE : E0 P.d (P.δ : ℝ) τ ≤ P.E) (hR : P.Realizable π)
    (hG : SubexpHard P.G.adv) (hLPN : SubexpHard (P.lpnFamily_raw π).adv) :
    SubexpHard (jlsSPRG_raw P π).adv ∧ (jlsSPRG_raw P π).HasComplexity P.d 2 ∧
      (jlsSPRG_raw P π).HasPolyStretch := sorry

/-- A secure raw structured-seed generator exists for every prime schedule
[JLS26, Theorem 4.1, p. 11]. Dv1 chooses a polynomial schedule; Dv3 assumes LPN
only for the construction's own families; Dv14 assumes realisability; Dv18 returns Raw.
SP-W1 uses rational δ; this statement does not claim a literal Definition 2.3 bridge.

**Proof sketch.** Choose E=max 1 E0, build Params from the given G and representation,
and apply theorem41 with the supplied family assumption and realisability. -/
theorem exists_sprg_raw {d cLoc : ℕ} (hd : 1 ≤ d) {δ : ℚ} {τ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hτ : 1 < τ) (G : BoolPRG)
    (R : G.MultilinearRep d) (hLoc : R.HasLocality cLoc) (hs : G.HasStretch τ)
    (hG : G.Secure) (π : PrimeSchedule)
    (hLPN : ∀ (E : ℕ) (hE : 1 ≤ E),
      (Params.lpnFamily_raw ⟨d, hd, δ, hδ, hδ1, E, hE, G, R⟩ π).Assumption)
    (hR : ∀ (E : ℕ) (hE : 1 ≤ E),
      (Params.Realizable ⟨d, hd, δ, hδ, hδ1, E, hE, G, R⟩ π)) :
    ∃ S : SPRG.Raw, (∀ κ, S.modulus κ = (π κ).p) ∧ S.Secure ∧
      S.HasComplexity d 2 ∧ S.HasPolyStretch := sorry

/-- A subexponentially secure raw generator exists for every prime schedule
[JLS26, Theorem 4.1, p. 11]. Dv13 uses a common subexponential advantage exponent;
Dv14 assumes realisability; Dv18 returns the raw bundle. SP-W1 uses rational δ.

**Proof sketch.** Choose the same sufficiently large schedule exponent and apply
 theorem41_subexp to the supplied family hardness and realisability. -/
theorem exists_sprg_raw_subexp {d cLoc : ℕ} (hd : 1 ≤ d) {δ : ℚ} {τ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hτ : 1 < τ) (G : BoolPRG)
    (R : G.MultilinearRep d) (hLoc : R.HasLocality cLoc) (hs : G.HasStretch τ)
    (hG : SubexpHard G.adv) (π : PrimeSchedule)
    (hLPN : ∀ (E : ℕ) (hE : 1 ≤ E),
      SubexpHard (Params.lpnFamily_raw ⟨d, hd, δ, hδ, hδ1, E, hE, G, R⟩ π).adv)
    (hR : ∀ (E : ℕ) (hE : 1 ≤ E),
      (Params.Realizable ⟨d, hd, δ, hδ, hδ1, E, hE, G, R⟩ π)) :
    ∃ S : SPRG.Raw, (∀ κ, S.modulus κ = (π κ).p) ∧ SubexpHard S.adv ∧
      S.HasComplexity d 2 ∧ S.HasPolyStretch := sorry

end TCSlib.Cryptography.Obfuscation.StructuredSeed
