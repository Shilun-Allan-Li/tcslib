/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Polys
import TCSlib.Cryptography.Obfuscation.StructuredSeed.SparseFactor
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exact-law draws and deterministic JLS seed cores

## Main definitions

* `Params.oneSd`, `Params.sdCore`: deterministic honest seed cores.
* Exact index and joint seed laws, and the concrete `Params.eval'` evaluator.
* `jlsSPRG_raw`: raw assembly with explicit finite coordinates and encodings.

## Main results

* Owner readers expose every algorithm, core field, and raw construction component.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026, §§2-4.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8 (non-uniform PPT adversaries).
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

open Complexity Turing
open scoped BigOperators
open TCSlib.Cryptography.Games

namespace Params

/-- An error coordinate is the residue produced by the canonical LPN scalar
core [JLS26, before Definition 2.3, p. 9]. Dv3 uses its exact finite seed;
the published seed-type equation transports the explicit draw. -/
noncomputable def noiseValue (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (c : Fin (P.W κ) × ZMod pp.p) : ZMod pp.p :=
  ((lpnNoise pp.p (P.W κ)).sample
    (cast (lpnNoise_coins pp.p (P.W κ)).symm c) : ZMod pp.p)

/-- Noise values read the canonical scalar core through its seed-type reader; glue. -/
theorem noiseValue_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (c : Fin (P.W κ) × ZMod pp.p) :
    P.noiseValue κ pp c = ((lpnNoise pp.p (P.W κ)).sample
      (cast (lpnNoise_coins pp.p (P.W κ)).symm c) : ZMod pp.p) := rfl

/-- ERR is the set of nonzero error coordinates [JLS26, 1SdSamp, p. 16].
Dv3 uses the transposed vector convention. -/
def errSet (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (e : Fin (P.n κ) → ZMod pp.p) : Finset (Fin (P.n κ)) :=
  Finset.univ.filter (fun i => e i ≠ 0)

/-- ERR is the nonzero-coordinate filter; glue. -/
theorem errSet_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (e : Fin (P.n κ) → ZMod pp.p) :
    P.errSet κ pp e = Finset.univ.filter (fun i => e i ≠ 0) := rfl

/-- BAD contains outputs whose representation uses an erroneous seed location
[JLS26, 1SdSamp, p. 16]. Dv4 reads locality on the multilinear representation. -/
noncomputable def badSet (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I : P.Idx' κ pp) (e : Fin (P.n κ) → ZMod pp.p) : Finset (Fin (P.m κ)) :=
  Finset.univ.filter fun j =>
    ((P.R.poly (P.n κ) I.1 (P.outputIndex κ j)).vars ∩ P.errSet κ pp e).Nonempty

/-- BAD is the finite dependency/error-intersection filter; glue. -/
theorem badSet_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I : P.Idx' κ pp) (e : Fin (P.n κ) → ZMod pp.p) :
    P.badSet κ pp I e = Finset.univ.filter fun j =>
      ((P.R.poly (P.n κ) I.1 (P.outputIndex κ j)).vars ∩ P.errSet κ pp e).Nonempty := rfl

/-- The one-instance success flag checks all three paper conditions
[JLS26, 1SdSamp, p. 16]. Dv3 uses rounded integer thresholds and the exact capacity. -/
noncomputable def oneFlag (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I : P.Idx' κ pp) (e : Fin (P.n κ) → ZMod pp.p) : Bool :=
  decide ((P.badSet κ pp I e).card ≤ P.Γ κ ∧
    ¬ (∃ b : Fin (P.B κ), P.cap κ < Buckets.load I.2.1 b) ∧
    ∀ b : Fin (P.B κ), (Buckets.bucket I.2.1 b ∩ P.badSet κ pp I e).card ≤ P.t κ)

/-- Success is the conjunction of bad-count, capacity, and per-bucket bounds; glue. -/
theorem oneFlag_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I : P.Idx' κ pp) (e : Fin (P.n κ) → ZMod pp.p) :
    P.oneFlag κ pp I e = decide ((P.badSet κ pp I e).card ≤ P.Γ κ ∧
      ¬ (∃ b : Fin (P.B κ), P.cap κ < Buckets.load I.2.1 b) ∧
      ∀ b : Fin (P.B κ), (Buckets.bucket I.2.1 b ∩ P.badSet κ pp I e).card ≤ P.t κ) := rfl

/-- The correction is the correct Boolean output minus the erroneous polynomial output
[JLS26, 1SdSamp, p. 16]. Dv3 casts the multilinear integer representation modulo p. -/
noncomputable def corr (P : Params) (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp)
    (σ : Fin (P.n κ) → Bool) (e : Fin (P.n κ) → ZMod pp.p)
    (j : Fin (P.m κ)) : ZMod pp.p :=
  ((P.G.eval (P.n κ) I.1 σ (P.outputIndex κ j)).toNat : ZMod pp.p) -
    MvPolynomial.eval₂ (Int.castRingHom (ZMod pp.p))
      (fun i => ((σ i).toNat : ZMod pp.p) + e i)
      (P.R.poly (P.n κ) I.1 (P.outputIndex κ j))

/-- Correction is the stated difference of correct and erroneous outputs; glue. -/
theorem corr_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp)
    (σ : Fin (P.n κ) → Bool) (e : Fin (P.n κ) → ZMod pp.p) (j : Fin (P.m κ)) :
    P.corr κ pp I σ e j =
      ((P.G.eval (P.n κ) I.1 σ (P.outputIndex κ j)).toNat : ZMod pp.p) -
        MvPolynomial.eval₂ (Int.castRingHom (ZMod pp.p))
          (fun i => ((σ i).toNat : ZMod pp.p) + e i)
          (P.R.poly (P.n κ) I.1 (P.outputIndex κ j)) := rfl

/-- A public LPN vector is A*s+e+σ [JLS26, 1SdSamp, p. 16].
Dv3 uses rows as samples and the canonical scalar-noise core. -/
noncomputable def lpnVector (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (A : Matrix (Fin (P.n κ)) (Fin (P.ℓ κ)) (ZMod pp.p))
    (σ : Fin (P.n κ) → Bool) (s : Fin (P.ℓ κ) → ZMod pp.p)
    (r : Fin (P.n κ) → Fin (P.W κ) × ZMod pp.p) : Fin (P.n κ) → ZMod pp.p :=
  fun i => (∑ a, A i a * s a) + P.noiseValue κ pp (r i) + ((σ i).toNat : ZMod pp.p)

/-- The LPN vector is its matrix-vector, error and Boolean-offset formula; glue. -/
theorem lpnVector_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (A : Matrix (Fin (P.n κ)) (Fin (P.ℓ κ)) (ZMod pp.p))
    (σ : Fin (P.n κ) → Bool) (s : Fin (P.ℓ κ) → ZMod pp.p)
    (r : Fin (P.n κ) → Fin (P.W κ) × ZMod pp.p) :
    P.lpnVector κ pp A σ s r = fun i =>
      (∑ a, A i a * s a) + P.noiseValue κ pp (r i) + ((σ i).toNat : ZMod pp.p) := rfl

/-- A one-instance seed records its success flag, LPN public vector, and compressed
private data [JLS26, 1SdSamp, p. 16]. Dv15 retains structured private coordinates. -/
structure OneSdOut (P : Params) (κ : ℕ) (pp : PrimeParam κ) where
  flag : Bool
  pub : Fin (P.n κ) → ZMod pp.p
  priv : P.SVar κ → ZMod pp.p

/-- One-instance sampling is a deterministic core on σ, secret and noise seeds
[JLS26, 1SdSamp, p. 16]. Dv3 transposes A; Dv17 uses an exact finite draw;
Dv15 uses a deterministic sparse factorization and structured coordinates. -/
noncomputable def oneSd (P : Params) (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp)
    (σ : Fin (P.n κ) → Bool) (s : Fin (P.ℓ κ) → ZMod pp.p)
    (r : Fin (P.n κ) → Fin (P.W κ) × ZMod pp.p) : P.OneSdOut κ pp :=
  let e := fun i => P.noiseValue κ pp (r i)
  let flag := P.oneFlag κ pp I e
  let factors := fun b => if flag then
    sparseFactor (Buckets.bucketMatrix I.2.1 (P.rc κ) (P.corr κ pp I σ e) b) (P.t κ)
    else (0, 0)
  { flag := flag
    pub := P.lpnVector κ pp I.2.2 σ s r
    priv := fun v => match v with
      | .inl α => ∏ a, if h : (α a).val < P.ℓ κ then s ⟨(α a).val, h⟩ else 1
      | .inr (b, .inl (i, a)) => (factors b).1 i a
      | .inr (b, .inr (a, j)) => (factors b).2 a j }

/-- The one-instance flag is the three-condition success test; glue. -/
theorem oneSd_flag (P : Params) (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp)
    (σ : Fin (P.n κ) → Bool) (s : Fin (P.ℓ κ) → ZMod pp.p)
    (r : Fin (P.n κ) → Fin (P.W κ) × ZMod pp.p) :
    (P.oneSd κ pp I σ s r).flag = P.oneFlag κ pp I (fun i => P.noiseValue κ pp (r i)) :=
  rfl

/-- The one-instance public vector is A*s+e+σ; glue. -/
theorem oneSd_pub (P : Params) (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp)
    (σ : Fin (P.n κ) → Bool) (s : Fin (P.ℓ κ) → ZMod pp.p)
    (r : Fin (P.n κ) → Fin (P.W κ) × ZMod pp.p) :
    (P.oneSd κ pp I σ s r).pub = fun i =>
      (∑ a, I.2.2 i a * s a) + P.noiseValue κ pp (r i) + ((σ i).toNat : ZMod pp.p) := rfl

/-- The one-instance private vector consists of tensor entries and the conditional
sparse factors; glue. -/
theorem oneSd_priv (P : Params) (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp)
    (σ : Fin (P.n κ) → Bool) (s : Fin (P.ℓ κ) → ZMod pp.p)
    (r : Fin (P.n κ) → Fin (P.W κ) × ZMod pp.p) :
    (P.oneSd κ pp I σ s r).priv =
      let e := fun i => P.noiseValue κ pp (r i)
      let factors := fun b => if P.oneFlag κ pp I e then
        sparseFactor (Buckets.bucketMatrix I.2.1 (P.rc κ) (P.corr κ pp I σ e) b) (P.t κ)
        else (0, 0)
      fun v => match v with
        | .inl α => ∏ a, if h : (α a).val < P.ℓ κ then s ⟨(α a).val, h⟩ else 1
        | .inr (b, .inl (i, a)) => (factors b).1 i a
        | .inr (b, .inr (a, j)) => (factors b).2 a j := rfl

/-- The first successful repetition is found in increasing Fin order
[JLS26, SdSamp', p. 15]. This deterministic search introduces no advice or choice. -/
def firstGood {κ : ℕ} (flags : Fin κ → Bool) : Option (Fin κ) :=
  (List.finRange κ).find? flags

/-- The first successful repetition is the ordered find operation; glue. -/
theorem firstGood_eq {κ : ℕ} (flags : Fin κ → Bool) :
    firstGood flags = (List.finRange κ).find? flags := rfl

/-- Pack the public blocks and error flag, and private flag/S/flag*S triples
[JLS26, SdSamp', pp. 15-16]. Dv15 uses the explicit public/private equivalences;
Dv10 precomputes flag*S so the evaluation remains private degree two. -/
noncomputable def packSeed (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (instances : Fin κ → P.OneSdOut κ pp) (first : Option (Fin κ)) : P.Seed κ pp :=
  (fun i => match (P.pubEquiv κ).symm i with
      | .inl (k, q) => (instances k).pub q
      | .inr _ => (first.isNone.toNat : ZMod pp.p),
   fun i => match (P.privEquiv κ).symm i with
      | (k, .inl _) => if first = some k then 1 else 0
      | (k, .inr (.inl v)) => (instances k).priv v
      | (k, .inr (.inr v)) =>
          (if first = some k then 1 else 0) * (instances k).priv v)

/-- The packed public vector reads instance blocks and the no-success flag; glue. -/
theorem packSeed_fst (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (instances : Fin κ → P.OneSdOut κ pp) (first : Option (Fin κ)) :
    (P.packSeed κ pp instances first).1 = fun i => match (P.pubEquiv κ).symm i with
      | .inl (k, q) => (instances k).pub q
      | .inr _ => (first.isNone.toNat : ZMod pp.p) := rfl

/-- The packed private vector is the flag/S/flag*S triple in Fin order; glue. -/
theorem packSeed_snd (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (instances : Fin κ → P.OneSdOut κ pp) (first : Option (Fin κ)) :
    (P.packSeed κ pp instances first).2 = fun i => match (P.privEquiv κ).symm i with
      | (k, .inl _) => if first = some k then 1 else 0
      | (k, .inr (.inl v)) => (instances k).priv v
      | (k, .inr (.inr v)) =>
          (if first = some k then 1 else 0) * (instances k).priv v := rfl

/-- A full core output retains the original Boolean seed, repetitions, selected index,
error flag and packed seed [JLS26, SdSamp', pp. 15-16]. These extra proof-facing fields
are not published to the adversary; Dv17 keeps the exact draw visible for coupling. -/
structure SdCoreOut (P : Params) (κ : ℕ) (pp : PrimeParam κ) where
  σ : Fin (P.n κ) → Bool
  draw : P.Draw κ pp
  instances : Fin κ → P.OneSdOut κ pp
  first : Option (Fin κ)
  err : Bool
  seed : P.Seed κ pp

/-- SdSamp's deterministic core runs the κ repetitions and selects their first success
[JLS26, SdSamp', pp. 15-16]. Dv17 maps one exact joint draw; no sampler is implemented. -/
noncomputable def sdCore (P : Params) (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp)
    (d : P.Draw κ pp) : P.SdCoreOut κ pp :=
  let instances := fun k => P.oneSd κ pp I d.1 (d.2 k).1 (d.2 k).2
  let first := firstGood (fun k => (instances k).flag)
  { σ := d.1, draw := d, instances := instances, first := first, err := first.isNone
    seed := P.packSeed κ pp instances first }

/-- The original Boolean seed is retained by sdCore; glue. -/
theorem sdCore_σ (P : Params) (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp)
    (d : P.Draw κ pp) : (P.sdCore κ pp I d).σ = d.1 := rfl

/-- The full exact draw is retained by sdCore for coupling arguments; glue. -/
theorem sdCore_draw (P : Params) (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp)
    (d : P.Draw κ pp) : (P.sdCore κ pp I d).draw = d := rfl

/-- The repetition outputs are exactly the oneSd cores; glue. -/
theorem sdCore_instances (P : Params) (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp)
    (d : P.Draw κ pp) : (P.sdCore κ pp I d).instances =
      fun k => P.oneSd κ pp I d.1 (d.2 k).1 (d.2 k).2 := rfl

/-- The selected repetition is the ordered first-success search; glue. -/
theorem sdCore_first (P : Params) (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp)
    (d : P.Draw κ pp) : (P.sdCore κ pp I d).first =
      firstGood (fun k => (P.oneSd κ pp I d.1 (d.2 k).1 (d.2 k).2).flag) := rfl

/-- The error flag is true exactly when no repetition succeeds; glue. -/
theorem sdCore_err (P : Params) (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp)
    (d : P.Draw κ pp) : (P.sdCore κ pp I d).err =
      (firstGood (fun k => (P.oneSd κ pp I d.1 (d.2 k).1 (d.2 k).2).flag)).isNone := rfl

/-- The core's seed is the explicit packed output; glue. -/
theorem sdCore_seed (P : Params) (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp)
    (d : P.Draw κ pp) : (P.sdCore κ pp I d).seed = P.packSeed κ pp
      (fun k => P.oneSd κ pp I d.1 (d.2 k).1 (d.2 k).2)
      (firstGood (fun k => (P.oneSd κ pp I d.1 (d.2 k).1 (d.2 k).2).flag)) := rfl

/-- IdSamp's core maps the Boolean generator's draw to I and keeps the other draws
[JLS26, IdSamp', p. 15]. Dv17 ties index sampling to its actual uniform joint draw. -/
noncomputable def idCore (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (d : P.IdDraw κ pp) : P.Idx' κ pp := (P.G.idCore (P.n κ) d.1, d.2)

/-- IdSamp's core maps only its Boolean-generator component; glue. -/
theorem idCore_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ) (d : P.IdDraw κ pp) :
    P.idCore κ pp d = (P.G.idCore (P.n κ) d.1, d.2) := rfl

/-- IdSamp' is the exact law of its one joint uniform draw and core
[JLS26, IdSamp', p. 15]. Dv17 postpones fair-coin realization to a target. -/
noncomputable def idSamp' (P : Params) (κ : ℕ) (pp : PrimeParam κ) : ProbComp (P.Idx' κ pp) :=
  P.idCore κ pp <$> ProbComp.sample (P.IdDraw κ pp)

/-- The index sampler is the pushforward of its explicit joint draw; glue. -/
theorem idSamp'_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ) :
    P.idSamp' κ pp = P.idCore κ pp <$> ProbComp.sample (P.IdDraw κ pp) := rfl

/-- The full seed law retains the core's proof-facing outputs
[JLS26, SdSamp', pp. 15-16]. Dv17 is an exact uniform pushforward. -/
noncomputable def sdSampFull (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I : P.Idx' κ pp) : ProbComp (P.SdCoreOut κ pp) :=
  P.sdCore κ pp I <$> ProbComp.sample (P.Draw κ pp)

/-- Full seed sampling maps sdCore over the uniform joint draw; glue. -/
theorem sdSampFull_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp) :
    P.sdSampFull κ pp I = P.sdCore κ pp I <$> ProbComp.sample (P.Draw κ pp) := rfl

/-- SdSamp' returns the seed projection of the full core law
[JLS26, SdSamp', pp. 15-16]. Dv17 preserves the exact joint distribution. -/
noncomputable def sdSamp' (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I : P.Idx' κ pp) : ProbComp (P.Seed κ pp) :=
  (fun x => x.seed) <$> P.sdSampFull κ pp I

/-- The seed law is the seed projection of the full law; glue. -/
theorem sdSamp'_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp) :
    P.sdSamp' κ pp I = (fun x => x.seed) <$> P.sdSampFull κ pp I := rfl

/-- Eval' evaluates G4 and recognizes the field value one
[JLS26, Eval', pp. 16-17]. Dv10 follows public degree d on p. 17, rather
than the overview's d+1; correctness proves its value is always Boolean on sampled seeds. -/
noncomputable def eval' (P : Params) (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp)
    (sd : P.Seed κ pp) : Fin (P.m κ) → Bool :=
  fun j => decide (MvPolynomial.eval (Sum.elim sd.1 sd.2) (P.G4 κ pp I j) = 1)

/-- Eval' recognizes one in each evaluated G4 coordinate; glue. -/
theorem eval'_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp)
    (sd : P.Seed κ pp) :
    P.eval' κ pp I sd = fun j =>
      decide (MvPolynomial.eval (Sum.elim sd.1 sd.2) (P.G4 κ pp I j) = 1) := rfl

/-- The construction challenge publishes pp, index, public seed and Boolean output
[JLS26, Definition 3.2, p. 10; Proposition 4.1, pp. 18-19]. Dv9 prepends pp;
Dv15 uses the fixed public-vector encoding. -/
noncomputable def challengeStr (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I : P.Idx' κ pp) (pub : Fin (P.pubLen κ) → ZMod pp.p)
    (z : Fin (P.m κ) → Bool) : List Bool :=
  pairEncode pp.enc (pairEncode (P.encIdx' κ pp I)
    (pairEncode (Encoding.Modular.encodeVector (κ + 1) pub) (List.ofFn z)))

/-- Construction challenges have the stated nested public layout; glue. -/
theorem challengeStr_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I : P.Idx' κ pp) (pub : Fin (P.pubLen κ) → ZMod pp.p)
    (z : Fin (P.m κ) → Bool) :
    P.challengeStr κ pp I pub z = pairEncode pp.enc (pairEncode (P.encIdx' κ pp I)
      (pairEncode (Encoding.Modular.encodeVector (κ + 1) pub) (List.ofFn z))) := rfl

/-- A public prime fits the syntactic residue width κ+1; glue for the raw assembly.

**Proof sketch.** Read the variable, constant and addition equations of PolyExpr, then
use the public parameter's upper width field. -/
theorem primeWidthBound (κ : ℕ) (pp : PrimeParam κ) :
    pp.p ≤ 2 ^ (PolyExpr.add .var (.const 1)).eval κ := sorry

end Params

/-- The JLS construction is a raw algorithm bundle [JLS26, construction,
pp. 15-17]. Dv1-Dv3 fix the polynomial schedule, field vectors and rounded
exact laws; Dv9 supplies an arbitrary prime schedule; Dv15 uses explicit
finite coordinates; Dv17-Dv18 add no sampler or efficiency proof here.
SP-W1 uses rational δ throughout. The primitive is assembled only from targets. -/
noncomputable def jlsSPRG_raw (P : Params) (π : PrimeSchedule) : SPRG.Raw where
  modulus κ := (π κ).p
  modulus_prime κ := (π κ).prime
  residueBits := .add .var (.const 1)
  modulus_le_pow κ := Params.primeWidthBound κ (π κ)
  Idx κ := P.Idx' κ (π κ)
  idxFintype _κ := inferInstance
  idxNonempty _κ := inferInstance
  idxCard κ := P.idxCard κ (π κ)
  idxEquiv κ := P.idxEquiv κ (π κ)
  IdDraw κ := P.IdDraw κ (π κ)
  idDrawFintype _κ := inferInstance
  idDrawNonempty _κ := inferInstance
  idDrawCard κ := P.idDrawCard κ (π κ)
  idDrawEquiv κ := P.idDrawEquiv κ (π κ)
  idCore κ := P.idCore κ (π κ)
  encIdDraw κ := P.encIdDraw κ (π κ)
  encIdDraw_injective κ := P.encIdDraw_injective κ (π κ)
  encIdx κ := P.encIdx' κ (π κ)
  encIdx_injective κ := P.encIdx'_injective κ (π κ)
  idxBits := P.idxBound
  encIdx_length_le κ := P.encIdx'_length_le κ (π κ)
  pubLen := P.pubLen
  privLen := P.privLen
  outLen := P.m
  seedBound := P.seedBound
  outBound := P.mBound
  pubLen_le := P.pubLen_le_seedBound
  privLen_le := P.privLen_le_seedBound
  outLen_le := P.m_le_mBound
  SdDraw κ _ := P.Draw κ (π κ)
  sdDrawFintype _κ _ := inferInstance
  sdDrawNonempty _κ _ := inferInstance
  sdDrawCard κ _ := P.drawCard κ (π κ)
  sdDrawEquiv κ _ := P.drawEquiv κ (π κ)
  sdCore κ I d := (P.sdCore κ (π κ) I d).seed
  encSdDraw κ _ := P.encDraw κ (π κ)
  encSdDraw_injective κ _ := P.encDraw_injective κ (π κ)
  eval κ := P.eval' κ (π κ)

/-- The raw construction is exactly the displayed record of algorithms, encodings,
finite coordinates and proved numeric field obligations; glue reader.

**Proof sketch.** The owner definition is the same record, so every field agrees
definitionally; reflexivity closes the equation. -/
theorem jlsSPRG_raw_eq (P : Params) (π : PrimeSchedule) :
    jlsSPRG_raw P π = {
  modulus κ := (π κ).p
  modulus_prime κ := (π κ).prime
  residueBits := .add .var (.const 1)
  modulus_le_pow κ := Params.primeWidthBound κ (π κ)
  Idx κ := P.Idx' κ (π κ)
  idxFintype _κ := inferInstance
  idxNonempty _κ := inferInstance
  idxCard κ := P.idxCard κ (π κ)
  idxEquiv κ := P.idxEquiv κ (π κ)
  IdDraw κ := P.IdDraw κ (π κ)
  idDrawFintype _κ := inferInstance
  idDrawNonempty _κ := inferInstance
  idDrawCard κ := P.idDrawCard κ (π κ)
  idDrawEquiv κ := P.idDrawEquiv κ (π κ)
  idCore κ := P.idCore κ (π κ)
  encIdDraw κ := P.encIdDraw κ (π κ)
  encIdDraw_injective κ := P.encIdDraw_injective κ (π κ)
  encIdx κ := P.encIdx' κ (π κ)
  encIdx_injective κ := P.encIdx'_injective κ (π κ)
  idxBits := P.idxBound
  encIdx_length_le κ := P.encIdx'_length_le κ (π κ)
  pubLen := P.pubLen
  privLen := P.privLen
  outLen := P.m
  seedBound := P.seedBound
  outBound := P.mBound
  pubLen_le := P.pubLen_le_seedBound
  privLen_le := P.privLen_le_seedBound
  outLen_le := P.m_le_mBound
  SdDraw κ _ := P.Draw κ (π κ)
  sdDrawFintype _κ _ := inferInstance
  sdDrawNonempty _κ _ := inferInstance
  sdDrawCard κ _ := P.drawCard κ (π κ)
  sdDrawEquiv κ _ := P.drawEquiv κ (π κ)
  sdCore κ I d := (P.sdCore κ (π κ) I d).seed
  encSdDraw κ _ := P.encDraw κ (π κ)
  encSdDraw_injective κ _ := P.encDraw_injective κ (π κ)
  eval κ := P.eval' κ (π κ) } := rfl

/-- The raw construction's modulus is the supplied schedule; glue. -/
theorem jlsSPRG_raw_modulus (P : Params) (π : PrimeSchedule) (κ : ℕ) :
    (jlsSPRG_raw P π).modulus κ = (π κ).p := rfl

/-- The raw residue-width polynomial is κ+1; glue. -/
theorem jlsSPRG_raw_residueBits (P : Params) (π : PrimeSchedule) :
    (jlsSPRG_raw P π).residueBits = .add .var (.const 1) := rfl

/-- The raw construction's index type is the concrete JLS triple; glue. -/
theorem jlsSPRG_raw_Idx (P : Params) (π : PrimeSchedule) (κ : ℕ) :
    (jlsSPRG_raw P π).Idx κ = P.Idx' κ (π κ) := rfl

/-- The raw construction's index draw is the concrete joint draw; glue. -/
theorem jlsSPRG_raw_IdDraw (P : Params) (π : PrimeSchedule) (κ : ℕ) :
    (jlsSPRG_raw P π).IdDraw κ = P.IdDraw κ (π κ) := rfl

/-- The raw construction's public length is the explicit packed length; glue. -/
theorem jlsSPRG_raw_pubLen (P : Params) (π : PrimeSchedule) (κ : ℕ) :
    (jlsSPRG_raw P π).pubLen κ = P.pubLen κ := rfl

/-- The raw construction's private length is the explicit packed length; glue. -/
theorem jlsSPRG_raw_privLen (P : Params) (π : PrimeSchedule) (κ : ℕ) :
    (jlsSPRG_raw P π).privLen κ = P.privLen κ := rfl

/-- The raw construction's output length is the Boolean generator's schedule; glue. -/
theorem jlsSPRG_raw_outLen (P : Params) (π : PrimeSchedule) (κ : ℕ) :
    (jlsSPRG_raw P π).outLen κ = P.m κ := rfl

/-- The raw index encoding is the explicit concrete encoding; glue. -/
theorem jlsSPRG_raw_encIdx (P : Params) (π : PrimeSchedule) (κ : ℕ)
    (I : P.Idx' κ (π κ)) : (jlsSPRG_raw P π).encIdx κ I = P.encIdx' κ (π κ) I := rfl

/-- The raw index core is the concrete core; glue. -/
theorem jlsSPRG_raw_idCore (P : Params) (π : PrimeSchedule) (κ : ℕ)
    (d : P.IdDraw κ (π κ)) : (jlsSPRG_raw P π).idCore κ d = P.idCore κ (π κ) d := rfl

/-- The raw index-draw encoding is the concrete joint-draw code; glue. -/
theorem jlsSPRG_raw_encIdDraw (P : Params) (π : PrimeSchedule) (κ : ℕ)
    (d : P.IdDraw κ (π κ)) :
    (jlsSPRG_raw P π).encIdDraw κ d = P.encIdDraw κ (π κ) d := rfl

/-- The raw seed draw is the concrete joint draw, independent of index; glue. -/
theorem jlsSPRG_raw_SdDraw (P : Params) (π : PrimeSchedule) (κ : ℕ)
    (I : P.Idx' κ (π κ)) : (jlsSPRG_raw P π).SdDraw κ I = P.Draw κ (π κ) := rfl

/-- The raw seed core returns the concrete packed seed; glue. -/
theorem jlsSPRG_raw_sdCore (P : Params) (π : PrimeSchedule) (κ : ℕ)
    (I : P.Idx' κ (π κ)) (d : P.Draw κ (π κ)) :
    (jlsSPRG_raw P π).sdCore κ I d = (P.sdCore κ (π κ) I d).seed := rfl

/-- The raw seed-draw encoding is the concrete joint-draw code; glue. -/
theorem jlsSPRG_raw_encSdDraw (P : Params) (π : PrimeSchedule) (κ : ℕ)
    (I : P.Idx' κ (π κ)) (d : P.Draw κ (π κ)) :
    (jlsSPRG_raw P π).encSdDraw κ I d = P.encDraw κ (π κ) d := rfl

/-- The raw evaluation algorithm is the concrete G4 evaluator; glue. -/
theorem jlsSPRG_raw_eval (P : Params) (π : PrimeSchedule) (κ : ℕ)
    (I : P.Idx' κ (π κ)) (sd : P.Seed κ (π κ)) :
    (jlsSPRG_raw P π).eval κ I sd = P.eval' κ (π κ) I sd := rfl

/-- The raw index sampler equals IdSamp'; glue.

**Proof sketch.** Read the raw sampler and concrete sampler equations, then use the
raw construction's index-draw and core fields. -/
theorem jlsSPRG_raw_idSamp (P : Params) (π : PrimeSchedule) (κ : ℕ) :
    (jlsSPRG_raw P π).idSamp κ = P.idSamp' κ (π κ) := by
  rw [SPRG.Raw.idSamp_eq]
  simp only [SPRG.Raw.instIdDrawFintype_eq]
  rfl

/-- The raw seed sampler equals SdSamp'; glue.

**Proof sketch.** Read both pushforward laws and compose the full core with its seed projection. -/
theorem jlsSPRG_raw_sdSamp (P : Params) (π : PrimeSchedule) (κ : ℕ)
    (I : P.Idx' κ (π κ)) :
    (jlsSPRG_raw P π).sdSamp κ I = P.sdSamp' κ (π κ) I := by
  rw [SPRG.Raw.sdSamp_eq, Params.sdSamp'_eq, Params.sdSampFull_eq, ← comp_map]
  simp only [SPRG.Raw.instSdDrawFintype_eq]
  rfl

/-- The raw challenge's modulus prefix equals the input prime encoding; glue.

**Proof sketch.** Read encPP and the construction's residue-width and modulus fields,
then the variable/addition equations of PolyExpr and PrimeParam.enc_eq. -/
theorem jlsSPRG_raw_encPP (P : Params) (π : PrimeSchedule) (κ : ℕ) :
    (jlsSPRG_raw P π).encPP κ = (π κ).enc := by
  rw [SPRG.Raw.encPP_eq, jlsSPRG_raw_residueBits, jlsSPRG_raw_modulus,
    PrimeParam.enc_eq]
  simp only [PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]

end TCSlib.Cryptography.Obfuscation.StructuredSeed
