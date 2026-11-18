/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Correctness
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

import Mathlib.Algebra.Order.Floor.Semifield

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial stretch of the JLS construction

## Main definitions

* `E0` gives the explicit sufficient polynomial schedule exponent.
* `Params.seedBitsAt` is the public/private field-vector payload bit count.

## Main results

* `Params.seedBitsAt_le` bounds the payload uniformly in every public prime.
* `jls_seedBits_le` reads the same bound on the raw construction.
* `jls_hasPolyStretch` states Claim 4.1 for the fixed polynomial schedule.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026,
  Claim 4.1 and its proof, p. 18.

Dv1 fixes one security parameter and a polynomial input-length schedule. Dv2 counts
field-vector payload bits; Dv3 fixes exact integral rounding; Dv5 uses the Boolean
stretch lower bound. The explicit threshold below is convention C10. SP-W1 uses
rational delta as construction data, coerced to real values in these analytic bounds.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8 (non-uniform PPT adversaries).
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

/-- A sufficient schedule exponent is
`E0 d delta tau = floor(max(10/delta,5/(tau-1)))+1`.
[JLS26, Claim 4.1, p. 18]. Dv1 makes sufficiently large polynomial seed length an
explicit condition on E. Convention C10 uses a deliberately generous fifth-power
seed bound; d is retained in the interface although this sufficient threshold is
independent of it when d≥1. SP-W1 coerces the construction's rational delta to real. -/
noncomputable def E0 (_d : ℕ) (δ τ : ℝ) : ℕ :=
  ⌊max (10 / δ) (5 / (τ - 1))⌋₊ + 1

/-- The sufficient exponent is its stated real-power comparison threshold; glue. -/
theorem E0_eq (d : ℕ) (δ τ : ℝ) :
    E0 d δ τ = ⌊max (10 / δ) (5 / (τ - 1))⌋₊ + 1 := rfl

namespace Params

/-- The construction's seed payload has
`seedBitsAt kappa = (pubLen kappa + privLen kappa)*(kappa+1)` bits.
[JLS26, proof of Claim 4.1, p. 18]. Dv2 uses fixed-width field vectors. Dv9's
arbitrary public prime changes no width, so this count is uniform in that prime. -/
noncomputable def seedBitsAt (P : Params) (κ : ℕ) : ℕ :=
  (P.pubLen κ + P.privLen κ) * (κ + 1)

/-- The payload count is the total coordinate count times kappa+1; glue. -/
theorem seedBitsAt_eq (P : Params) (κ : ℕ) :
    P.seedBitsAt κ = (P.pubLen κ + P.privLen κ) * (κ + 1) := rfl

/-- The seed payload is at most `C*(kappa+1)^5*(n+m/w+1)` for a fixed natural C,
uniformly over every kappa and every public prime. [JLS26, proof of Claim 4.1, p. 18].
Dv1 fixes the polynomial schedule; Dv2-Dv3 replace the asymptotic expression by this
explicit integral upper bound. Natural division and the final one cover rounding
and the zero-parameter boundary. SP-W1 uses rational delta.

**Proof sketch.** Count the repeated public vectors, flags, tensor coordinates and two
factor arrays. Bound the rounded bucket count by its quotient plus one, and cancel
one noise-width factor against W=w^2 in the factor-array term. Bound the tensor
term by a degree-dependent constant times n, absorb rounding terms using w≤ell+1,
and enlarge the fixed constant to cover the finitely many boundary cases. -/
theorem seedBitsAt_le (P : Params) :
    ∃ C : ℕ, ∀ κ,
      P.seedBitsAt κ ≤ C * (κ + 1) ^ 5 * (P.n κ + P.m κ / P.w κ + 1) := sorry

end Params

/-- The raw construction's seed-bit function equals the prime-independent payload count.
[JLS26, proof of Claim 4.1, p. 18]. Dv1-Dv2 and Dv9 fix the family and residue width.

**Proof sketch.** Read SPRG.Raw.seedBits through its published equation, then use the
construction's public/private length and residue-width field readers. -/
theorem jls_seedBits_eq (P : Params) (π : PrimeSchedule) (κ : ℕ) :
    (jlsSPRG_raw P π).seedBits κ = P.seedBitsAt κ := sorry

/-- The raw construction has seed length at most
`C*(kappa+1)^5*(n+m/w+1)` at every parameter. [JLS26, proof of Claim 4.1, p. 18].
Dv1-Dv3 make the schedule, field widths and exact rounding explicit; the constant can
be chosen independently of the public prime schedule.

**Proof sketch.** Apply the prime-independent payload estimate and read the raw
construction's bit count through jls_seedBits_eq. -/
theorem jls_seedBits_le (P : Params) (π : PrimeSchedule) :
    ∃ C : ℕ, ∀ κ,
      (jlsSPRG_raw P π).seedBits κ ≤
        C * (κ + 1) ^ 5 * (P.n κ + P.m κ / P.w κ + 1) := sorry

/-- The raw construction has polynomial stretch when its schedule exponent is at least E0.
[JLS26, Claim 4.1, p. 18]. Dv1 replaces sufficiently large polynomial seed length by
`E0 d delta tau ≤ E`; Dv3 uses rounded noise and Dv5 uses the input stretch lower bound.
SP-W1 supplies rational delta, coerced to real for the threshold. Dv18 keeps this
stretch theorem on the raw bundle; honest efficiency is supplied by the later assembly.
SP-W3 requires eventual seed growth as well as the power bound.

**Proof sketch.** Read the sufficient exponent to obtain E*delta/2>5 and E*(tau-1)>5.
Apply the fifth-power payload bound. The rounded noise width eventually grows like
ell^(delta/2), so both n and m/w leave a positive power gap below m after the kappa^5
factor. Use the polynomial output upper bound to choose one fixed stretch exponent
strictly above one, and absorb the fixed constant beyond a common threshold.
The public length is at least one, so its κ+1-bit residue width also gives
κ+1 ≤ seedBits at every κ and supplies the seed-growth conjunct. -/
theorem jls_hasPolyStretch (P : Params) (π : PrimeSchedule) {τ : ℝ} (hτ : 1 < τ)
    (hs : P.G.HasStretch τ) (hE : E0 P.d (P.δ : ℝ) τ ≤ P.E) :
    (jlsSPRG_raw P π).HasPolyStretch := sorry

end TCSlib.Cryptography.Obfuscation.StructuredSeed
