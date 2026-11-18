/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Security
import TCSlib.Cryptography.CoinSampling.Contract

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Phase B targets, realisability links, and primitive assembly

## Main definitions

* `Params.evalTarget` through `Params.lpnSamplerTarget`: obligations T1-T6.
* `Params.Targets`: their conjunction, with uniform algorithms chosen before inputs.
* `jlsSPRG`, `Params.lpnFamily`: the only primitive assemblies, from target witnesses.

## Main results

* `Params.realizable_of_targets`: target-to-realiser link via the shared API.
* `theorem41_of_targets` and efficient primitive existence corollaries.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026, §§2-4.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8 (non-uniform PPT adversaries).
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

open Complexity Turing
open TCSlib.Cryptography.CoinSampling

namespace Params

/-- A seed-sampler input consists of its public prime and function index
[JLS26, Definition 3.1, p. 10]. Dv9 and Dv17 expose these as the shared contract's
parameter rather than asking an algorithm to compute the prime. -/
abbrev SdParam (P : Params) (κ : ℕ) : Type := Σ pp : PrimeParam κ, P.Idx' κ pp

/-- The seed-sampler parameter is its prime/index dependent pair; glue. -/
theorem sdParam_eq (P : Params) (κ : ℕ) :
    P.SdParam κ = (Σ pp : PrimeParam κ, P.Idx' κ pp) := rfl

/-- The index-sampler parameter word starts with pp and includes unary κ
[JLS26, Definition 3.1, p. 10]. Dv9 and Dv17 keep public inputs explicit. -/
def idWord (_P : Params) (κ : ℕ) (pp : PrimeParam κ) : List Bool :=
  pairEncode pp.enc (List.replicate κ true)

/-- The index word is pp paired with unary κ; glue. -/
theorem idWord_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ) :
    P.idWord κ pp = pairEncode pp.enc (List.replicate κ true) := rfl

/-- The seed-sampler word starts with pp, then unary κ and index
[JLS26, Definition 3.1, p. 10]. Dv17 indexes one exact joint draw by this public word. -/
noncomputable def sdWord (P : Params) (κ : ℕ) (q : P.SdParam κ) : List Bool :=
  pairEncode q.1.enc (pairEncode (List.replicate κ true) (P.encIdx' κ q.1 q.2))

/-- The seed word carries pp, unary κ and the concrete index code; glue. -/
theorem sdWord_eq (P : Params) (κ : ℕ) (q : P.SdParam κ) :
    P.sdWord κ q = pairEncode q.1.enc
      (pairEncode (List.replicate κ true) (P.encIdx' κ q.1 q.2)) := rfl

/-- T1 requires one uniform map for Eval' on every κ and input prime
[JLS26, Definition 3.1, p. 10; Eval', pp. 16-17]. Dv9 and Dv18 defer efficiency.
Phase B obligation; not proved in this development. -/
def evalTarget (P : Params) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ κ (pp : PrimeParam κ) (I : P.Idx' κ pp) (sd : P.Seed κ pp),
      f (NUPPT.advInput κ (pairEncode pp.enc
        (pairEncode (P.encIdx' κ pp I) (P.encSeed' κ pp sd)))) =
          List.ofFn (P.eval' κ pp I sd)

/-- The target is its stated uniform contract; glue. -/
theorem evalTarget_iff (P : Params) : P.evalTarget ↔
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ κ (pp : PrimeParam κ) (I : P.Idx' κ pp) (sd : P.Seed κ pp),
      f (NUPPT.advInput κ (pairEncode pp.enc
        (pairEncode (P.encIdx' κ pp I) (P.encSeed' κ pp sd)))) =
          List.ofFn (P.eval' κ pp I sd) := Iff.rfl

/-- T2 requires uniform generation of a term list denoting each G4 output polynomial
[JLS26, Definition 3.3, p. 10; Equation (4), p. 17]. Dv6 uses composite polynomials,
Dv15 uses explicit Fin coordinates, and Dv18 defers generation efficiency.
Phase B obligation; not proved in this development. -/
def qGenTarget (P : Params) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ κ (pp : PrimeParam κ) (I : P.Idx' κ pp) (j : Fin (P.m κ)),
      ∃ ts : PolyTerms (Fin (P.pubLen κ) ⊕ Fin (P.privLen κ)) (ZMod pp.p),
        f (NUPPT.advInput κ (pairEncode pp.enc
          (pairEncode (P.encIdx' κ pp I) (PolyTerms.encFin j)))) =
            PolyTerms.encTerms (fun z => Candidates.natToList (κ + 1) z.val)
              (fun v => PolyTerms.encFin (finSumFinEquiv v)) ts ∧
        PolyTerms.denote ts = P.G4 κ pp I j

/-- The target is its stated uniform contract; glue. -/
theorem qGenTarget_iff (P : Params) : P.qGenTarget ↔
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ κ (pp : PrimeParam κ) (I : P.Idx' κ pp) (j : Fin (P.m κ)),
      ∃ ts : PolyTerms (Fin (P.pubLen κ) ⊕ Fin (P.privLen κ)) (ZMod pp.p),
        f (NUPPT.advInput κ (pairEncode pp.enc
          (pairEncode (P.encIdx' κ pp I) (PolyTerms.encFin j)))) =
            PolyTerms.encTerms (fun z => Candidates.natToList (κ + 1) z.val)
              (fun v => PolyTerms.encFin (finSumFinEquiv v)) ts ∧
        PolyTerms.denote ts = P.G4 κ pp I j := Iff.rfl

/-- T3 requires uniform computability of the actual index and seed cores
[JLS26, IdSamp' and SdSamp', pp. 15-16]. Dv17-Dv18 use the shared CoreComputable
halves on the same joint draws as T5, without constructing any sampler.
Phase B obligation; not proved in this development. -/
def coreTarget (P : Params) : Prop :=
  CoreComputable (P := PrimeParam)
      (fun κ pp => P.idWord κ pp) (fun κ pp => P.encIdDraw κ pp)
      (fun κ pp => P.encIdx' κ pp) (fun κ pp => P.idCore κ pp) ∧
    CoreComputable (P := P.SdParam)
      (fun κ q => P.sdWord κ q) (fun κ q => P.encDraw κ q.1)
      (fun κ q => P.encSeed' κ q.1)
      (fun κ q d => (P.sdCore κ q.1 q.2 d).seed)

/-- The target is its stated uniform contract; glue. -/
theorem coreTarget_iff (P : Params) : P.coreTarget ↔
  CoreComputable (P := PrimeParam)
      (fun κ pp => P.idWord κ pp) (fun κ pp => P.encIdDraw κ pp)
      (fun κ pp => P.encIdx' κ pp) (fun κ pp => P.idCore κ pp) ∧
    CoreComputable (P := P.SdParam)
      (fun κ q => P.sdWord κ q) (fun κ q => P.encDraw κ q.1)
      (fun κ q => P.encSeed' κ q.1)
      (fun κ q d => (P.sdCore κ q.1 q.2 d).seed) := Iff.rfl

/-- T4 requires one uniform preprocessing map for every LPN schedule and advice
[JLS26, Lemma 4.2, p. 19]. Dv12 puts all averaging choices and pp in the advice input;
Dv14 defers efficiency and never samples inside the reduction.
Phase B obligation; not proved in this development. -/
def lpnPreTarget (P : Params) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ (π : PrimeSchedule) L (ω : P.LPNAdvice π L) (x : P.LPNChal π L),
      f (pairEncode (P.encLPNAdvice π L ω) (P.lpnEnc π L x)) = P.lpnPre π L ω x

/-- The target is its stated uniform contract; glue. -/
theorem lpnPreTarget_iff (P : Params) : P.lpnPreTarget ↔
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ (π : PrimeSchedule) L (ω : P.LPNAdvice π L) (x : P.LPNChal π L),
      f (pairEncode (P.encLPNAdvice π L ω) (P.lpnEnc π L x)) = P.lpnPre π L ω x := Iff.rfl

/-- T4 requires one uniform preprocessing map for every PRG schedule and advice
[JLS26, Lemma 4.2, p. 19]. Dv12 carries pp and the averaging choices on the advice input;
Dv14 defers efficiency and constructs no machine.
Phase B obligation; not proved in this development. -/
def prgPreTarget (P : Params) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ (π : PrimeSchedule) N (ω : P.PRGAdvice π N) (x : P.PRGChal N),
      f (pairEncode (P.encPRGAdvice π N ω) (P.prgEnc N x)) = P.prgPre π N ω x

/-- The target is its stated uniform contract; glue. -/
theorem prgPreTarget_iff (P : Params) : P.prgPreTarget ↔
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ (π : PrimeSchedule) N (ω : P.PRGAdvice π N) (x : P.PRGChal N),
      f (pairEncode (P.encPRGAdvice π N ω) (P.prgEnc N x)) = P.prgPre π N ω x := Iff.rfl

/-- The reduction targets are the two uniform preprocessing obligations
[JLS26, Lemma 4.2, p. 19]. Dv14 separates these from the security inequality.
Phase B obligation; not proved in this development. -/
def ReductionTargets (P : Params) : Prop :=
  P.lpnPreTarget ∧ P.prgPreTarget

/-- The target is its stated uniform contract; glue. -/
theorem reductionTargets_iff (P : Params) : P.ReductionTargets ↔
  P.lpnPreTarget ∧ P.prgPreTarget := Iff.rfl

/-- T5 requires fair-coin samplability of each complete exact draw
[JLS26, IdSamp' and SdSamp', pp. 15-16]. Dv17-Dv18 use the shared DrawSamplable halves.
Each target concerns one draw type, even when that type is a product.
Phase B obligation; not proved in this development. -/
def drawSamplerTarget (P : Params) : Prop :=
  DrawSamplable (P := PrimeParam)
      (fun κ pp => P.idWord κ pp) (fun κ pp => P.encIdDraw κ pp) ∧
    DrawSamplable (P := P.SdParam)
      (fun κ q => P.sdWord κ q) (fun κ q => P.encDraw κ q.1)

/-- The target is its stated uniform contract; glue. -/
theorem drawSamplerTarget_iff (P : Params) : P.drawSamplerTarget ↔
  DrawSamplable (P := PrimeParam)
      (fun κ pp => P.idWord κ pp) (fun κ pp => P.encIdDraw κ pp) ∧
    DrawSamplable (P := P.SdParam)
      (fun κ q => P.sdWord κ q) (fun κ q => P.encDraw κ q.1) := Iff.rfl

/-- T6 requires uniform efficient sampling of the construction's joint LPN draw and core
[JLS26, Definition 2.3, pp. 9-10]. Dv3 uses its own rounded family; Dv9 passes the prime
on the parameter word. The sampler and map are quantified before the schedule, which
is the shared contract's parameter, and do not compute it. Dv17-Dv18 keep the exact law.
Phase B obligation; not proved in this development. -/
def lpnSamplerTarget (P : Params) : Prop :=
  SamplesEfficiently (P := fun _ => PrimeSchedule)
    (fun L π => (P.lpnFamily_raw π).sampleWord L)
    (fun L π => (P.lpnFamily_raw π).encDraw L)
    (fun L π => (P.lpnFamily_raw π).encSample L)
    (fun L π => (P.lpnFamily_raw π).sampleCore L)

/-- The target is its stated uniform contract; glue. -/
theorem lpnSamplerTarget_iff (P : Params) : P.lpnSamplerTarget ↔
  SamplesEfficiently (P := fun _ => PrimeSchedule)
    (fun L π => (P.lpnFamily_raw π).sampleWord L)
    (fun L π => (P.lpnFamily_raw π).encDraw L)
    (fun L π => (P.lpnFamily_raw π).encSample L)
    (fun L π => (P.lpnFamily_raw π).sampleCore L) := Iff.rfl

/-- The six efficiency obligations jointly inhabit the raw construction as a primitive
[JLS26, Definitions 3.1-3.3, p. 10; construction, pp. 15-17]. Dv18 keeps all efficiency
proofs in these targets, while every inhabited primitive carries their consequences.
Phase B obligation; not proved in this development. -/
def Targets (P : Params) : Prop :=
  P.evalTarget ∧ P.qGenTarget ∧ P.coreTarget ∧ P.ReductionTargets ∧
    P.drawSamplerTarget ∧ P.lpnSamplerTarget

/-- The target is its stated uniform contract; glue. -/
theorem targets_iff (P : Params) : P.Targets ↔
  P.evalTarget ∧ P.qGenTarget ∧ P.coreTarget ∧ P.ReductionTargets ∧
    P.drawSamplerTarget ∧ P.lpnSamplerTarget := Iff.rfl

/-- The preprocessing targets give realisers for every schedule and advice family
[JLS26, Lemma 4.2, p. 19]. Dv14 discharges realisability from target hypotheses;
Dv16 uses the shared layout-coin RealizesOn predicate and its public link theorem.

**Proof sketch.** For each reduction, specialize its single preprocessing map at π.
Apply exists_realizesOn_of_preTarget with the inverse parameter map, polynomial var,
the explicit advice encoding and length bound. Match the named reduction by its reader. -/
theorem realizable_of_targets (P : Params) (hT : P.ReductionTargets) :
    ∀ π : PrimeSchedule, P.Realizable π := sorry

/-- T1 gives the raw evaluator's uniform efficiency; glue.

**Proof sketch.** Specialize the target at pp=π κ and read the raw construction's encodings. -/
theorem evalEfficient_of_target (P : Params) (π : PrimeSchedule) (hT : P.evalTarget) :
    (jlsSPRG_raw P π).EvalEfficient := sorry

/-- T3 and T5 give the exact index sampler's efficiency through the shared contract; glue.

**Proof sketch.** Read the draw and core witnesses, restrict public parameters to π κ,
and join them with SamplesEfficiently.intro, using the raw field readers. -/
theorem idSampEfficient_of_targets (P : Params) (π : PrimeSchedule)
    (hC : P.coreTarget) (hD : P.drawSamplerTarget) :
    SamplesEfficiently (P := fun _ => Unit)
      (fun κ _ => (jlsSPRG_raw P π).idWord κ)
      (fun κ _ => (jlsSPRG_raw P π).encIdDraw κ)
      (fun κ _ => (jlsSPRG_raw P π).encIdx κ)
      (fun κ _ => (jlsSPRG_raw P π).idCore κ) := sorry

/-- T3 and T5 give the exact seed sampler's efficiency through the shared contract; glue.

**Proof sketch.** Restrict the universal pp/index parameter to the supplied schedule.
Read the unchanged core and encoding witnesses and join the two shared contract halves. -/
theorem sdSampEfficient_of_targets (P : Params) (π : PrimeSchedule)
    (hC : P.coreTarget) (hD : P.drawSamplerTarget) :
    SamplesEfficiently (P := (jlsSPRG_raw P π).Idx)
      (fun κ I => (jlsSPRG_raw P π).sdWord κ I)
      (fun κ I => (jlsSPRG_raw P π).encSdDraw κ I)
      (fun κ _ => (jlsSPRG_raw P π).encSeed κ)
      (fun κ I => (jlsSPRG_raw P π).sdCore κ I) := sorry

/-- T6 specializes to the sampler field of each raw LPN family; glue.

**Proof sketch.** Read the universal schedule-parametrized witness and specialize its
equivalence and equations at π. Retain the same uniform sampler, polynomial and map. -/
theorem lpnSamplerEfficient_of_target (P : Params) (π : PrimeSchedule)
    (hT : P.lpnSamplerTarget) :
    SamplesEfficiently (P := fun _ => Unit)
      (fun L _ => (P.lpnFamily_raw π).sampleWord L)
      (fun L _ => (P.lpnFamily_raw π).encDraw L)
      (fun L _ => (P.lpnFamily_raw π).encSample L)
      (fun L _ => (P.lpnFamily_raw π).sampleCore L) := sorry

/-- The construction's LPN primitive is assembled from its raw family and T6
[JLS26, Definition 2.3, pp. 9-10]. Dv18 requires this efficiency witness for any instance. -/
noncomputable def lpnFamily (P : Params) (π : PrimeSchedule) (hT : P.Targets) :
    LPNFamily where
  toRaw := P.lpnFamily_raw π
  sample_eff := P.lpnSamplerEfficient_of_target π hT.2.2.2.2.2

/-- The assembled LPN primitive has exactly the specified raw family; glue. -/
theorem lpnFamily_toRaw (P : Params) (π : PrimeSchedule) (hT : P.Targets) :
    (P.lpnFamily π hT).toRaw = P.lpnFamily_raw π := rfl

/-- T2 generates the bidegree-bounded G4 output polynomials
[JLS26, Definition 3.3, p. 10; Equation (4), p. 17]. Dv6 uses the composite form.

**Proof sketch.** Use G4 as the polynomial witness, the target's term-list equations,
its degree theorem, and exact sampled-seed correctness. -/
theorem hasComplexityEff_of_target (P : Params) (π : PrimeSchedule)
    (hT : P.qGenTarget) : (jlsSPRG_raw P π).HasComplexityEff P.d 2 := sorry

end Params

/-- The efficient JLS sPRG is assembled from the raw algorithms and targets
[JLS26, construction, pp. 15-17]. Dv18 makes efficiency mandatory: no primitive
value is supplied without its evaluator and two sampler witnesses. -/
noncomputable def jlsSPRG (P : Params) (π : PrimeSchedule) (hT : P.Targets) : SPRG where
  toRaw := jlsSPRG_raw P π
  eval_eff := P.evalEfficient_of_target π hT.1
  idSamp_eff := P.idSampEfficient_of_targets π hT.2.2.1 hT.2.2.2.2.1
  sdSamp_eff := P.sdSampEfficient_of_targets π hT.2.2.1 hT.2.2.2.2.1

/-- The assembled primitive's raw bundle is exactly jlsSPRG_raw; glue. -/
theorem jlsSPRG_toRaw (P : Params) (π : PrimeSchedule) (hT : P.Targets) :
    (jlsSPRG P π hT).toRaw = jlsSPRG_raw P π := rfl

/-- The targets give a secure primitive with efficient (d,2) complexity and stretch
[JLS26, Theorem 4.1, p. 11]. Dv3 assumes the construction's own LPN family;
Dv6 uses composite bidegree; Dv9 allows every prime schedule; Dv18 assembles efficiency.
SP-W1 uses rational δ, coerced to real values in the schedule threshold.

**Proof sketch.** Targets provide realisability and the primitive's honest efficiency.
Apply the raw theorem, transport its properties through jlsSPRG_toRaw, and use T2 for
efficient polynomial generation. -/
theorem theorem41_of_targets (P : Params) (π : PrimeSchedule) {cLoc : ℕ} {τ : ℝ}
    (hLoc : P.R.HasLocality cLoc) (hτ : 1 < τ) (hs : P.G.HasStretch τ)
    (hE : E0 P.d (P.δ : ℝ) τ ≤ P.E) (hT : P.Targets)
    (hG : P.G.Secure) (hLPN : (P.lpnFamily_raw π).Assumption) :
    (jlsSPRG P π hT).Secure ∧ (jlsSPRG P π hT).HasComplexityEff P.d 2 ∧
      (jlsSPRG P π hT).HasPolyStretch := sorry

/-- Under the efficiency targets an efficient secure sPRG exists
[JLS26, Theorem 4.1, p. 11]. Dv3 uses the construction's own LPN families; Dv18
inhabits the primitive from targets rather than asserting unproved efficiency.
SP-W1 restricts δ to rational data.

**Proof sketch.** Choose E=max 1 E0, specialize the targets to those parameters, and apply
 theorem41_of_targets to the given Boolean PRG and construction-family assumption. -/
theorem exists_sprg_of_targets {d cLoc : ℕ} (hd : 1 ≤ d) {δ : ℚ} {τ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hτ : 1 < τ) (G : BoolPRG)
    (R : G.MultilinearRep d) (hLoc : R.HasLocality cLoc) (hs : G.HasStretch τ)
    (hG : G.Secure) (π : PrimeSchedule)
    (hLPN : ∀ (E : ℕ) (hE : 1 ≤ E),
      (Params.lpnFamily_raw ⟨d, hd, δ, hδ, hδ1, E, hE, G, R⟩ π).Assumption)
    (hT : ∀ P : Params, P.Targets) :
    ∃ S : SPRG, (∀ κ, S.modulus κ = (π κ).p) ∧ S.Secure ∧
      S.HasComplexityEff d 2 ∧ S.HasPolyStretch := sorry

/-- Under the targets and subexponential assumptions an efficient subexponentially secure
sPRG exists [JLS26, Theorem 4.1, p. 11]. Dv13 bounds advantage against NUPPT;
Dv18 requires the honest efficiency fields. SP-W1 uses rational δ.

**Proof sketch.** Choose a sufficiently large E, use the raw subexponential theorem and
T2, then assemble the primitive from the specialized target witnesses. -/
theorem exists_sprg_of_targets_subexp {d cLoc : ℕ} (hd : 1 ≤ d) {δ : ℚ} {τ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hτ : 1 < τ) (G : BoolPRG)
    (R : G.MultilinearRep d) (hLoc : R.HasLocality cLoc) (hs : G.HasStretch τ)
    (hG : SubexpHard G.adv) (π : PrimeSchedule)
    (hLPN : ∀ (E : ℕ) (hE : 1 ≤ E),
      SubexpHard (Params.lpnFamily_raw ⟨d, hd, δ, hδ, hδ1, E, hE, G, R⟩ π).adv)
    (hT : ∀ P : Params, P.Targets) :
    ∃ S : SPRG, (∀ κ, S.modulus κ = (π κ).p) ∧ SubexpHard S.adv ∧
      S.HasComplexityEff d 2 ∧ S.HasPolyStretch := sorry

end TCSlib.Cryptography.Obfuscation.StructuredSeed
