/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Degree
import TCSlib.Cryptography.Obfuscation.StructuredSeed.PolyTerms
import TCSlib.Cryptography.CoinSampling.Contract
import TCSlib.Cryptography.Encoding.Modular
import TCSlib.Cryptography.Foundations.Subexponential
import Mathlib.NumberTheory.Bertrand

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Structured-seed PRG syntax, security, complexity, and efficiency

## Main definitions

* `PrimeParam`, `PrimeSchedule`: public prime inputs and non-vacuous schedules.
* `SPRG.Raw`: exact algorithms and their correctness/security predicates.
* `SPRG`: the primitive with mandatory uniform evaluator and sampler efficiency.

## Main results

* `PrimeSchedule.nonempty` proves schedule non-vacuity.
* The owner readers expose games, encodings, stretch, and complexity contracts.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026, §§2-4.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8 (non-uniform PPT adversaries).
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

open Complexity Turing
open TCSlib.Cryptography.Games
open TCSlib.Cryptography.CoinSampling

/-- A public prime has `2^κ ≤ p ≤ 2^(κ+1)` [JLS26, Definition 3.3, p. 10;
§4, p. 15]. Dv9: the prime is an input, rather than a computed schedule; the
boundary κ = 0 admits p = 2. No algorithm chooses a prime. -/
structure PrimeParam (κ : ℕ) where
  p : ℕ
  prime : p.Prime
  two_pow_le : 2 ^ κ ≤ p
  le_two_pow : p ≤ 2 ^ (κ + 1)

instance PrimeParam.instNeZero {κ : ℕ} (pp : PrimeParam κ) : NeZero pp.p :=
  ⟨pp.prime.ne_zero⟩

instance PrimeParam.instFact {κ : ℕ} (pp : PrimeParam κ) : Fact pp.p.Prime :=
  ⟨pp.prime⟩

/-- The public numeral is p in κ+2 bits [JLS26, §4, p. 15]. Dv9: the extra
bit includes the κ=0 boundary and makes the parameter public on the wire. -/
def PrimeParam.enc {κ : ℕ} (pp : PrimeParam κ) : List Bool :=
  Candidates.natToList (κ + 2) pp.p

/-- The encoding is `natToList (κ+2) p`; glue. -/
theorem PrimeParam.enc_eq {κ : ℕ} (pp : PrimeParam κ) :
    pp.enc = Candidates.natToList (κ + 2) pp.p := rfl

/-- A prime schedule assigns one public prime to every κ [JLS26,
Definition 3.3, p. 10]. Dv9: no computability is assumed; results quantify
all schedules and honest algorithms receive each prime as input. -/
abbrev PrimeSchedule : Type := (κ : ℕ) → PrimeParam κ

/-- A schedule is a function selecting a PrimeParam at every κ; glue. -/
theorem primeSchedule_eq : PrimeSchedule = ((κ : ℕ) → PrimeParam κ) := rfl

/-- A schedule exists by Bertrand's postulate; glue for non-vacuity of
[JLS26, Definition 3.3, p. 10]. This existence is never a prime algorithm.

**Proof sketch.** Apply Bertrand to 2^κ, use its strict lower bound as the
required weak bound, and rewrite twice 2^κ as 2^(κ+1). -/
theorem PrimeSchedule.nonempty : Nonempty PrimeSchedule := by
  classical
  let h := fun κ : ℕ =>
    Nat.exists_prime_lt_and_le_two_mul (2 ^ κ) (pow_ne_zero κ (Nat.succ_ne_zero 1))
  refine ⟨fun κ => ⟨Classical.choose (h κ), (Classical.choose_spec (h κ)).1,
    (Classical.choose_spec (h κ)).2.1.le, ?_⟩⟩
  simpa only [pow_succ, Nat.mul_comm] using (Classical.choose_spec (h κ)).2.2

namespace SPRG

/-- An exact-law structured-seed algorithm bundle over a public prime
[JLS26, Definitions 3.1-3.3, p. 10]. Dv1-Dv2 and Dv15: one parameter and
Fin-indexed field-vector seeds. Dv17-Dv18: draws and deterministic cores
specify exact laws; efficiency is added by SPRG, never asserted by Raw.
The public modulus is carried on every sPRG challenge (Dv9). -/
structure Raw where
  modulus : ℕ → ℕ
  modulus_prime : ∀ κ, (modulus κ).Prime
  residueBits : PolyExpr
  modulus_le_pow : ∀ κ, modulus κ ≤ 2 ^ residueBits.eval κ
  Idx : ℕ → Type
  idxFintype : ∀ κ, Fintype (Idx κ)
  idxNonempty : ∀ κ, Nonempty (Idx κ)
  idxCard : ℕ → ℕ
  idxEquiv : ∀ κ, Idx κ ≃ Fin (idxCard κ)
  IdDraw : ℕ → Type
  idDrawFintype : ∀ κ, Fintype (IdDraw κ)
  idDrawNonempty : ∀ κ, Nonempty (IdDraw κ)
  idDrawCard : ℕ → ℕ
  idDrawEquiv : ∀ κ, IdDraw κ ≃ Fin (idDrawCard κ)
  idCore : (κ : ℕ) → IdDraw κ → Idx κ
  encIdDraw : (κ : ℕ) → IdDraw κ → List Bool
  encIdDraw_injective : ∀ κ, Function.Injective (encIdDraw κ)
  encIdx : (κ : ℕ) → Idx κ → List Bool
  encIdx_injective : ∀ κ, Function.Injective (encIdx κ)
  idxBits : PolyExpr
  encIdx_length_le : ∀ κ I, (encIdx κ I).length ≤ idxBits.eval κ
  pubLen : ℕ → ℕ
  privLen : ℕ → ℕ
  outLen : ℕ → ℕ
  seedBound : PolyExpr
  outBound : PolyExpr
  pubLen_le : ∀ κ, pubLen κ ≤ seedBound.eval κ
  privLen_le : ∀ κ, privLen κ ≤ seedBound.eval κ
  outLen_le : ∀ κ, outLen κ ≤ outBound.eval κ
  SdDraw : (κ : ℕ) → Idx κ → Type
  sdDrawFintype : ∀ κ I, Fintype (SdDraw κ I)
  sdDrawNonempty : ∀ κ I, Nonempty (SdDraw κ I)
  sdDrawCard : (κ : ℕ) → Idx κ → ℕ
  sdDrawEquiv : ∀ κ I, SdDraw κ I ≃ Fin (sdDrawCard κ I)
  sdCore : (κ : ℕ) → (I : Idx κ) → SdDraw κ I →
    (Fin (pubLen κ) → ZMod (modulus κ)) × (Fin (privLen κ) → ZMod (modulus κ))
  encSdDraw : (κ : ℕ) → (I : Idx κ) → SdDraw κ I → List Bool
  encSdDraw_injective : ∀ κ I, Function.Injective (encSdDraw κ I)
  eval : (κ : ℕ) → Idx κ →
    ((Fin (pubLen κ) → ZMod (modulus κ)) ×
      (Fin (privLen κ) → ZMod (modulus κ))) → Fin (outLen κ) → Bool

namespace Raw

instance instIdxFintype (S : Raw) (κ : ℕ) : Fintype (S.Idx κ) := S.idxFintype κ
instance instIdxNonempty (S : Raw) (κ : ℕ) : Nonempty (S.Idx κ) := S.idxNonempty κ
instance instIdDrawFintype (S : Raw) (κ : ℕ) : Fintype (S.IdDraw κ) := S.idDrawFintype κ
instance instIdDrawNonempty (S : Raw) (κ : ℕ) : Nonempty (S.IdDraw κ) :=
  S.idDrawNonempty κ
instance instSdDrawFintype (S : Raw) (κ : ℕ) (I : S.Idx κ) : Fintype (S.SdDraw κ I) :=
  S.sdDrawFintype κ I
instance instSdDrawNonempty (S : Raw) (κ : ℕ) (I : S.Idx κ) : Nonempty (S.SdDraw κ I) :=
  S.sdDrawNonempty κ I
instance instModulusNeZero (S : Raw) (κ : ℕ) : NeZero (S.modulus κ) :=
  ⟨(S.modulus_prime κ).ne_zero⟩

/-- The index finiteness instance is its stored raw field; glue. -/
theorem instIdxFintype_eq (S : Raw) (κ : ℕ) :
    instIdxFintype S κ = S.idxFintype κ := rfl

/-- The index-draw finiteness instance is its stored raw field; glue. -/
theorem instIdDrawFintype_eq (S : Raw) (κ : ℕ) :
    instIdDrawFintype S κ = S.idDrawFintype κ := rfl

/-- The seed-draw finiteness instance is its stored raw field; glue. -/
theorem instSdDrawFintype_eq (S : Raw) (κ : ℕ) (I : S.Idx κ) :
    instSdDrawFintype S κ I = S.sdDrawFintype κ I := rfl

/-- The seed is a public/private vector pair [JLS26, Definition 3.1,
p. 10]. Dv2 and Dv15 use fixed-width field vectors, indexed by Fin. -/
abbrev Seed (S : Raw) (κ : ℕ) : Type :=
  (Fin (S.pubLen κ) → ZMod (S.modulus κ)) ×
    (Fin (S.privLen κ) → ZMod (S.modulus κ))

/-- The seed type is the public/private pair; glue. -/
theorem seed_eq (S : Raw) (κ : ℕ) : S.Seed κ =
    ((Fin (S.pubLen κ) → ZMod (S.modulus κ)) ×
      (Fin (S.privLen κ) → ZMod (S.modulus κ))) := rfl

/-- IdSamp is the exact pushforward of the index draw [JLS26,
Definition 3.1, p. 10]. Dv17-Dv18: the sampler contract is separate. -/
noncomputable def idSamp (S : Raw) (κ : ℕ) : ProbComp (S.Idx κ) :=
  S.idCore κ <$> ProbComp.sample (S.IdDraw κ)

/-- IdSamp maps idCore over the uniform draw; glue. -/
theorem idSamp_eq (S : Raw) (κ : ℕ) :
    S.idSamp κ = S.idCore κ <$> ProbComp.sample (S.IdDraw κ) := rfl

/-- SdSamp is the exact pushforward of the joint seed draw [JLS26,
Definition 3.1, p. 10]. Dv17-Dv18: no coin sampler is constructed. -/
noncomputable def sdSamp (S : Raw) (κ : ℕ) (I : S.Idx κ) : ProbComp (S.Seed κ) :=
  S.sdCore κ I <$> ProbComp.sample (S.SdDraw κ I)

/-- SdSamp maps sdCore over its one exact draw; glue. -/
theorem sdSamp_eq (S : Raw) (κ : ℕ) (I : S.Idx κ) :
    S.sdSamp κ I = S.sdCore κ I <$> ProbComp.sample (S.SdDraw κ I) := rfl

/-- The modulus is encoded in residueBits+1 bits [JLS26, Definition 3.3,
p. 10]. Dv9 makes the modulus public rather than computing it. -/
def encPP (S : Raw) (κ : ℕ) : List Bool :=
  Candidates.natToList (S.residueBits.eval κ + 1) (S.modulus κ)

/-- The public parameter is the fixed-width numeral; glue. -/
theorem encPP_eq (S : Raw) (κ : ℕ) :
    S.encPP κ = Candidates.natToList (S.residueBits.eval κ + 1) (S.modulus κ) := rfl

/-- Encode both field-vector seeds [JLS26, Definition 3.1, p. 10].
Dv2 and Dv15 fix increasing Fin-coordinate order. -/
def encSeed (S : Raw) (κ : ℕ) (sd : S.Seed κ) : List Bool :=
  pairEncode (Encoding.Modular.encodeVector (S.residueBits.eval κ) sd.1)
    (Encoding.Modular.encodeVector (S.residueBits.eval κ) sd.2)

/-- The seed encoding pairs the two vector encodings; glue. -/
theorem encSeed_eq (S : Raw) (κ : ℕ) (sd : S.Seed κ) :
    S.encSeed κ sd = pairEncode
      (Encoding.Modular.encodeVector (S.residueBits.eval κ) sd.1)
      (Encoding.Modular.encodeVector (S.residueBits.eval κ) sd.2) := rfl

/-- An sPRG challenge is pp, index, public seed, output [JLS26,
Definition 3.2, p. 10]. Dv9 prepends the public modulus. -/
def challengeStr (S : Raw) (κ : ℕ) (I : S.Idx κ)
    (pub : Fin (S.pubLen κ) → ZMod (S.modulus κ))
    (z : Fin (S.outLen κ) → Bool) : List Bool :=
  pairEncode (S.encPP κ) (pairEncode (S.encIdx κ I)
    (pairEncode (Encoding.Modular.encodeVector (S.residueBits.eval κ) pub) (List.ofFn z)))

/-- The challenge has pp as its first field; glue. -/
theorem challengeStr_eq (S : Raw) (κ : ℕ) (I : S.Idx κ)
    (pub : Fin (S.pubLen κ) → ZMod (S.modulus κ))
    (z : Fin (S.outLen κ) → Bool) :
    S.challengeStr κ I pub z = pairEncode (S.encPP κ) (pairEncode (S.encIdx κ I)
      (pairEncode (Encoding.Modular.encodeVector (S.residueBits.eval κ) pub)
        (List.ofFn z))) := rfl

/-- The real or random game samples index, joint seed and adversary coins
[JLS26, Definition 3.2, p. 10]. Dv1 uses κ alone; Dv9 publishes p. -/
noncomputable def game (S : Raw) (A : NUPPT) (real : Bool) (κ : ℕ) : ProbComp Bool :=
  (S.idSamp κ).bind fun I => (S.sdSamp κ I).bind fun sd =>
    (ProbComp.sample (Fin (S.outLen κ) → Bool)).bind fun z =>
    (ProbComp.sample (A.Coins κ)).bind fun r =>
    pure (A.distinguisherL κ (S.challengeStr κ I sd.1
      (if real then S.eval κ I sd else z)) r)

/-- The game is the stated sequence of exact laws; glue. -/
theorem game_eq (S : Raw) (A : NUPPT) (real : Bool) (κ : ℕ) :
    S.game A real κ = (S.idSamp κ).bind fun I => (S.sdSamp κ I).bind fun sd =>
      (ProbComp.sample (Fin (S.outLen κ) → Bool)).bind fun z =>
      (ProbComp.sample (A.Coins κ)).bind fun r =>
      pure (A.distinguisherL κ (S.challengeStr κ I sd.1
        (if real then S.eval κ I sd else z)) r) := rfl

/-- Advantage is the absolute real/random acceptance gap [JLS26,
Definition 3.2, p. 10; Definition 2.1, p. 9]. Dv13 uses NUPPT adversaries. -/
noncomputable def adv (S : Raw) (A : NUPPT) (κ : ℕ) : ℝ :=
  advantage (S.game A true κ) (S.game A false κ)

/-- Advantage is the game advantage; glue. -/
theorem adv_eq (S : Raw) (A : NUPPT) (κ : ℕ) :
    S.adv A κ = advantage (S.game A true κ) (S.game A false κ) := rfl

/-- Security means negligible advantage for every NUPPT [JLS26,
Definition 3.2, p. 10]. Dv13 fixes this adversary class. -/
def Secure (S : Raw) : Prop := ∀ A : NUPPT, Negligible (S.adv A)

/-- Security quantifies all NUPPT adversaries; glue. -/
theorem secure_iff (S : Raw) : S.Secure ↔ ∀ A : NUPPT, Negligible (S.adv A) := Iff.rfl

/-- Subexponential security is the shared SubexpHard predicate [JLS26,
Definition 2.1, p. 9]. Dv13 bounds advantage, not adversary running time. -/
def SubexpSecure (S : Raw) : Prop := SubexpHard S.adv

/-- Subexponential security is exactly SubexpHard; glue. -/
theorem subexpSecure_iff (S : Raw) : S.SubexpSecure ↔ SubexpHard S.adv := Iff.rfl

/-- Seed bit length is the total residue count times its width [JLS26,
Remark 3.2, p. 10]. Dv1-Dv2 count the single-index vector encoding. -/
def seedBits (S : Raw) (κ : ℕ) : ℕ :=
  (S.pubLen κ + S.privLen κ) * S.residueBits.eval κ

/-- Seed bits are (public+private length) times residueBits; glue. -/
theorem seedBits_eq (S : Raw) (κ : ℕ) :
    S.seedBits κ = (S.pubLen κ + S.privLen κ) * S.residueBits.eval κ := rfl

/-- Polynomial stretch expands seed bits by some exponent greater than one
[JLS26, Remark 3.1, p. 10]. Dv1 is the fixed polynomial schedule form.
SP-W3 also requires seed bits to be at least κ eventually, excluding constant-length
vacuity in the single-parameter existence statements. -/
def HasPolyStretch (S : Raw) : Prop :=
  ∃ τ : ℝ, 1 < τ ∧ ∃ κ₀, ∀ κ ≥ κ₀,
    κ ≤ S.seedBits κ ∧ (S.seedBits κ : ℝ) ^ τ ≤ S.outLen κ

/-- Polynomial stretch has eventual seed growth and a real-power output bound; glue. -/
theorem hasPolyStretch_iff (S : Raw) : S.HasPolyStretch ↔
    ∃ τ : ℝ, 1 < τ ∧ ∃ κ₀, ∀ κ ≥ κ₀,
      κ ≤ S.seedBits κ ∧ (S.seedBits κ : ℝ) ^ τ ≤ S.outLen κ := Iff.rfl

/-- Complexity is a bidegree-bounded polynomial on every sampled seed
[JLS26, Definition 3.3, p. 10]. Dv6 restricts the public class to degree
and uses one composite polynomial; Dv15 uses Fin variables. The predicate
quantifies every index, a strengthening of the support-only condition. -/
def HasComplexity (S : Raw) (dPub dPriv : ℕ) : Prop :=
  ∀ κ (I : S.Idx κ), ∃ Q : Fin (S.outLen κ) →
    MvPolynomial (Fin (S.pubLen κ) ⊕ Fin (S.privLen κ)) (ZMod (S.modulus κ)),
    (∀ j, pubDegree (Q j) ≤ dPub ∧ privDegree (Q j) ≤ dPriv) ∧
    (S.sdSamp κ I).AllOutputs fun sd => ∀ j,
      ((S.eval κ I sd j).toNat : ZMod (S.modulus κ)) =
        MvPolynomial.eval (Sum.elim sd.1 sd.2) (Q j)

/-- Complexity supplies the stated degree and evaluation witnesses; glue. -/
theorem hasComplexity_iff (S : Raw) (dPub dPriv : ℕ) :
    S.HasComplexity dPub dPriv ↔ ∀ κ (I : S.Idx κ), ∃ Q :
      Fin (S.outLen κ) → MvPolynomial (Fin (S.pubLen κ) ⊕ Fin (S.privLen κ))
        (ZMod (S.modulus κ)),
      (∀ j, pubDegree (Q j) ≤ dPub ∧ privDegree (Q j) ≤ dPriv) ∧
      (S.sdSamp κ I).AllOutputs fun sd => ∀ j,
        ((S.eval κ I sd j).toNat : ZMod (S.modulus κ)) =
          MvPolynomial.eval (Sum.elim sd.1 sd.2) (Q j) := Iff.rfl

/-- Eval efficiency is one uniform map with p on its input [JLS26,
Definition 3.1, p. 10]. Dv9 and Dv18 supply the modulus and defer proof. -/
def EvalEfficient (S : Raw) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∀ κ I sd,
    f (NUPPT.advInput κ (pairEncode (S.encPP κ)
      (pairEncode (S.encIdx κ I) (S.encSeed κ sd)))) = List.ofFn (S.eval κ I sd)

/-- Eval efficiency has its one-map characterization; glue. -/
theorem evalEfficient_iff (S : Raw) : S.EvalEfficient ↔
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∀ κ I sd,
      f (NUPPT.advInput κ (pairEncode (S.encPP κ)
        (pairEncode (S.encIdx κ I) (S.encSeed κ sd)))) = List.ofFn (S.eval κ I sd) :=
  Iff.rfl

/-- The sampler word contains unary κ and pp [JLS26, Definition 3.1,
p. 10]. Dv17: the shared sampler contract indexes draw types by this word. -/
def idWord (S : Raw) (κ : ℕ) : List Bool :=
  pairEncode (S.encPP κ) (List.replicate κ true)

/-- The index-draw word pairs pp and unary κ; glue. -/
theorem idWord_eq (S : Raw) (κ : ℕ) :
    S.idWord κ = pairEncode (S.encPP κ) (List.replicate κ true) := rfl

/-- The seed-sampler word contains pp, unary κ and index [JLS26,
Definition 3.1, p. 10]. Dv17 uses one jointly sampled draw. -/
def sdWord (S : Raw) (κ : ℕ) (I : S.Idx κ) : List Bool :=
  pairEncode (S.encPP κ) (pairEncode (List.replicate κ true) (S.encIdx κ I))

/-- The seed-draw word contains its public inputs; glue. -/
theorem sdWord_eq (S : Raw) (κ : ℕ) (I : S.Idx κ) :
    S.sdWord κ I = pairEncode (S.encPP κ)
      (pairEncode (List.replicate κ true) (S.encIdx κ I)) := rfl

/-- Efficient complexity generates the actual degree-bounded output
polynomials from pp and index [JLS26, Definition 3.3, p. 10]. Dv6 uses
finite term lists for the composite polynomial; Dv18 defers efficiency. -/
def HasComplexityEff (S : Raw) (dPub dPriv : ℕ) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∀ κ (I : S.Idx κ),
    ∃ Q : Fin (S.outLen κ) →
      MvPolynomial (Fin (S.pubLen κ) ⊕ Fin (S.privLen κ)) (ZMod (S.modulus κ)),
    (∀ j, ∃ ts : PolyTerms (Fin (S.pubLen κ) ⊕ Fin (S.privLen κ)) (ZMod (S.modulus κ)),
      f (NUPPT.advInput κ (pairEncode (S.encPP κ)
        (pairEncode (S.encIdx κ I) (PolyTerms.encFin j)))) =
        PolyTerms.encTerms (fun z => Candidates.natToList (S.residueBits.eval κ) z.val)
          (fun v => PolyTerms.encFin (finSumFinEquiv v)) ts ∧ PolyTerms.denote ts = Q j) ∧
    (∀ j, pubDegree (Q j) ≤ dPub ∧ privDegree (Q j) ≤ dPriv) ∧
    (S.sdSamp κ I).AllOutputs fun sd => ∀ j,
      ((S.eval κ I sd j).toNat : ZMod (S.modulus κ)) =
        MvPolynomial.eval (Sum.elim sd.1 sd.2) (Q j)

/-- Efficient complexity is exactly the term-list generation contract; glue. -/
theorem hasComplexityEff_iff (S : Raw) (dPub dPriv : ℕ) :
    S.HasComplexityEff dPub dPriv ↔
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∀ κ (I : S.Idx κ),
      ∃ Q : Fin (S.outLen κ) →
        MvPolynomial (Fin (S.pubLen κ) ⊕ Fin (S.privLen κ)) (ZMod (S.modulus κ)),
      (∀ j, ∃ ts : PolyTerms (Fin (S.pubLen κ) ⊕ Fin (S.privLen κ))
          (ZMod (S.modulus κ)),
        f (NUPPT.advInput κ (pairEncode (S.encPP κ)
          (pairEncode (S.encIdx κ I) (PolyTerms.encFin j)))) =
          PolyTerms.encTerms (fun z => Candidates.natToList (S.residueBits.eval κ) z.val)
            (fun v => PolyTerms.encFin (finSumFinEquiv v)) ts ∧ PolyTerms.denote ts = Q j) ∧
      (∀ j, pubDegree (Q j) ≤ dPub ∧ privDegree (Q j) ≤ dPriv) ∧
      (S.sdSamp κ I).AllOutputs fun sd => ∀ j,
        ((S.eval κ I sd j).toNat : ZMod (S.modulus κ)) =
          MvPolynomial.eval (Sum.elim sd.1 sd.2) (Q j) := Iff.rfl

/-- Efficient complexity implies complexity [JLS26, Definition 3.3,
p. 10]. This is glue forgetting the generation algorithm.

**Proof sketch.** Retain the polynomial, degree, and evaluation witnesses
and discard the uniform generator and its term-list equations. -/
theorem HasComplexityEff.hasComplexity {S : Raw} {dPub dPriv : ℕ}
    (h : S.HasComplexityEff dPub dPriv) : S.HasComplexity dPub dPriv := sorry

end Raw
end SPRG

/-- A structured-seed primitive carries all honest efficiency fields
[JLS26, Definition 3.1, p. 10]. Dv17-Dv18 add uniform exact-on-success
sampler contracts to the raw exact laws. No instance omits efficiency. -/
structure SPRG extends SPRG.Raw where
  eval_eff : toRaw.EvalEfficient
  idSamp_eff : SamplesEfficiently (P := fun _ => Unit)
    (fun κ _ => toRaw.idWord κ) (fun κ _ => encIdDraw κ)
    (fun κ _ => encIdx κ) (fun κ _ => idCore κ)
  sdSamp_eff : SamplesEfficiently (P := toRaw.Idx)
    (fun κ I => toRaw.sdWord κ I) (fun κ I => encSdDraw κ I)
    (fun κ _ => toRaw.encSeed κ) (fun κ I => sdCore κ I)

namespace SPRG

/-- Primitive security reads security of its raw bundle [JLS26,
Definition 3.2, p. 10]. Dv18 keeps algorithm and efficiency layers distinct. -/
def Secure (S : SPRG) : Prop := S.toRaw.Secure

/-- Primitive security is raw security; glue. -/
theorem secure_iff (S : SPRG) : S.Secure ↔ S.toRaw.Secure := Iff.rfl

/-- Primitive complexity reads raw complexity [JLS26, Definition 3.3,
p. 10]. Dv18 adds the honest efficiency fields separately. -/
def HasComplexity (S : SPRG) (dPub dPriv : ℕ) : Prop :=
  S.toRaw.HasComplexity dPub dPriv

/-- Primitive complexity is raw complexity; glue. -/
theorem hasComplexity_iff (S : SPRG) (dPub dPriv : ℕ) :
    S.HasComplexity dPub dPriv ↔ S.toRaw.HasComplexity dPub dPriv := Iff.rfl

/-- Primitive efficient complexity generates its output polynomials
[JLS26, Definition 3.3, p. 10]. Dv18 reads the raw predicate. -/
def HasComplexityEff (S : SPRG) (dPub dPriv : ℕ) : Prop :=
  S.toRaw.HasComplexityEff dPub dPriv

/-- Primitive efficient complexity is raw efficient complexity; glue. -/
theorem hasComplexityEff_iff (S : SPRG) (dPub dPriv : ℕ) :
    S.HasComplexityEff dPub dPriv ↔ S.toRaw.HasComplexityEff dPub dPriv := Iff.rfl

/-- Primitive stretch reads its raw seed-bit count [JLS26, Remark 3.1,
p. 10]. Dv18 adds efficiency without changing the lengths. -/
def HasPolyStretch (S : SPRG) : Prop := S.toRaw.HasPolyStretch

/-- Primitive stretch is raw stretch; glue. -/
theorem hasPolyStretch_iff (S : SPRG) : S.HasPolyStretch ↔ S.toRaw.HasPolyStretch := Iff.rfl

/-- Primitive advantage reads its raw game advantage [JLS26,
Definition 3.2, p. 10]. Dv18 changes no experiment. -/
noncomputable def adv (S : SPRG) (A : NUPPT) (κ : ℕ) : ℝ := S.toRaw.adv A κ

/-- Primitive advantage equals raw advantage; glue. -/
theorem adv_eq (S : SPRG) (A : NUPPT) (κ : ℕ) : S.adv A κ = S.toRaw.adv A κ := rfl

end SPRG
end TCSlib.Cryptography.Obfuscation.StructuredSeed
