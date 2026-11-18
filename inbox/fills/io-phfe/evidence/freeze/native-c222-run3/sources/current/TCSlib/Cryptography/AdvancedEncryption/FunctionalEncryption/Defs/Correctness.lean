/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Raw
import TCSlib.Cryptography.Games.Hopping

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exact functional-encryption algorithms and correctness

The honest algorithms sample their complete finite draw and apply the deterministic core.
The honest experiment generates public parameters, sets up keys, encrypts the public/private
input, and generates one function key. Its output retains the public parameters needed to
interpret the decryption result in the drawn group.

## Main definitions

* `FEScheme.Raw.pubGen`, `setup`, `enc`, `keyGen`: the exact honest algorithms.
* `FEScheme.Raw.HonestOutcome`, `honestRun`: one complete honest experiment.
* `FEScheme.Raw.Correct`, `CorrectExcept`: perfect and explicitly bounded correctness.

## Main results

* `FEScheme.Raw.Correct.correctExcept_zero`: perfect correctness implies zero error.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definitions 4.1-4.2.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing

variable {C : FnClass} (S : FEScheme.Raw C)

/-- Generate the group's public parameters, including its nonidentity generator
[GJLS21, Definition 4.1]. -/
noncomputable def pubGen (κ : ℕ) : ProbComp (PublicParams S.G κ) :=
  publicParamsGen S.G κ

/-- Public-parameter generation is the common exact group-parameter experiment. -/
theorem pubGen_eq (κ : ℕ) : S.pubGen κ = publicParamsGen S.G κ := rfl

/-- Setup applies its deterministic core to one uniform complete draw
[GJLS21, Definition 4.1]. -/
noncomputable def setup (κ : ℕ) (pp : PublicParams S.G κ) :
    ProbComp (S.MPK κ pp × S.MSK κ pp) :=
  S.setupCore κ pp <$> ProbComp.sample (S.SetupDraw κ pp)

/-- Setup is the pushforward of its uniform draw by its deterministic core. -/
theorem setup_eq (κ : ℕ) (pp : PublicParams S.G κ) :
    S.setup κ pp = S.setupCore κ pp <$> ProbComp.sample (S.SetupDraw κ pp) := rfl

/-- Encryption takes the public key and both input parts, then applies its core to one
uniform complete draw [GJLS21, Definition 4.1]. The public part is returned separately
to the adversary and decryption algorithm. -/
noncomputable def enc (κ : ℕ) (pp : PublicParams S.G κ) (pk : S.MPK κ pp)
    (x : Fin (C.pubLen.eval κ) → Bool) (y : Fin (C.privLen.eval κ) → Bool) :
    ProbComp (S.CT κ pp) :=
  S.encCore κ pp pk x y <$> ProbComp.sample (S.EncDraw κ pp pk x y)

/-- Encryption is the pushforward of its uniform draw by its deterministic core. -/
theorem enc_eq (κ : ℕ) (pp : PublicParams S.G κ) (pk : S.MPK κ pp)
    (x : Fin (C.pubLen.eval κ) → Bool) (y : Fin (C.privLen.eval κ) → Bool) :
    S.enc κ pp pk x y =
      S.encCore κ pp pk x y <$> ProbComp.sample (S.EncDraw κ pp pk x y) := rfl

/-- Key generation takes the master secret key and function description, then applies
its core to one uniform complete draw [GJLS21, Definition 4.1]. -/
noncomputable def keyGen (κ : ℕ) (pp : PublicParams S.G κ) (msk : S.MSK κ pp)
    (f : Fin (C.fnLen.eval κ) → Bool) : ProbComp (S.SK κ pp) :=
  S.keyCore κ pp msk f <$> ProbComp.sample (S.KeyDraw κ pp msk f)

/-- Key generation is the pushforward of its uniform draw by its deterministic core. -/
theorem keyGen_eq (κ : ℕ) (pp : PublicParams S.G κ) (msk : S.MSK κ pp)
    (f : Fin (C.fnLen.eval κ) → Bool) :
    S.keyGen κ pp msk f =
      S.keyCore κ pp msk f <$> ProbComp.sample (S.KeyDraw κ pp msk f) := rfl

/-- An honest outcome retains the public parameters, public key, function key and
ciphertext [GJLS21, Definition 4.2]. This record permits parameter-dependent group types
without installing an instance for a dependent-sum type. -/
structure HonestOutcome (κ : ℕ) where
  /-- The public parameters drawn before setup. -/
  pp : PublicParams S.G κ
  /-- The master public key from setup. -/
  pk : S.MPK κ pp
  /-- The function key generated from the corresponding master secret key. -/
  sk : S.SK κ pp
  /-- The encryption of the public and private inputs. -/
  ct : S.CT κ pp

/-- An honest experiment generates parameters and keys, encrypts the inputs, then produces
the function key [GJLS21, Definition 4.2]. -/
noncomputable def honestRun (κ : ℕ) (f : Fin (C.fnLen.eval κ) → Bool)
    (x : Fin (C.pubLen.eval κ) → Bool) (y : Fin (C.privLen.eval κ) → Bool) :
    ProbComp (S.HonestOutcome κ) :=
  (S.pubGen κ).bind fun pp =>
  (S.setup κ pp).bind fun k =>
  (S.enc κ pp k.1 x y).bind fun ct =>
  (fun sk => ⟨pp, k.1, sk, ct⟩) <$> S.keyGen κ pp k.2 f

/-- The honest experiment is the displayed sequencing of its four algorithms. -/
theorem honestRun_eq (κ : ℕ) (f : Fin (C.fnLen.eval κ) → Bool)
    (x : Fin (C.pubLen.eval κ) → Bool) (y : Fin (C.privLen.eval κ) → Bool) :
    S.honestRun κ f x y =
      (S.pubGen κ).bind fun pp =>
      (S.setup κ pp).bind fun k =>
      (S.enc κ pp k.1 x y).bind fun ct =>
      (fun sk => ⟨pp, k.1, sk, ct⟩) <$> S.keyGen κ pp k.2 f := rfl

/-- Perfect correctness means that every honest outcome decrypts to the embedded
function value [GJLS21, Definition 4.2], strengthened to zero error. -/
def Correct : Prop :=
  ∀ κ f x y, (S.honestRun κ f x y).AllOutputs fun o =>
    S.dec κ o.pp o.sk x o.ct = some (S.embed κ o.pp (C.eval κ (S.cprm κ o.pp) f x y))

/-- Perfect correctness is the displayed all-outcomes decryption identity. -/
theorem correct_iff : S.Correct ↔
    ∀ κ f x y, (S.honestRun κ f x y).AllOutputs fun o =>
      S.dec κ o.pp o.sk x o.ct =
        some (S.embed κ o.pp (C.eval κ (S.cprm κ o.pp) f x y)) := Iff.rfl

/-- Correctness with error at most `ε κ` bounds the probability of an incorrect or failed
decryption in every honest experiment [GJLS21, Definition 4.2]. -/
def CorrectExcept (ε : ℕ → ℝ) : Prop :=
  ∀ κ f x y, ProbComp.prob (S.honestRun κ f x y) (fun o =>
    S.dec κ o.pp o.sk x o.ct ≠
      some (S.embed κ o.pp (C.eval κ (S.cprm κ o.pp) f x y))) ≤ ε κ

/-- Bounded correctness is the displayed probability inequality for every input and key. -/
theorem correctExcept_iff (ε : ℕ → ℝ) : S.CorrectExcept ε ↔
    ∀ κ f x y, ProbComp.prob (S.honestRun κ f x y) (fun o =>
      S.dec κ o.pp o.sk x o.ct ≠
        some (S.embed κ o.pp (C.eval κ (S.cprm κ o.pp) f x y))) ≤ ε κ := Iff.rfl

/-- Perfect correctness implies correctness with error zero [GJLS21, Definition 4.2].

**Proof sketch.** The all-outcomes identity makes the incorrect-decryption event false
throughout the support of each honest run. Its probability is zero, so it satisfies the
required bound. -/
theorem Correct.correctExcept_zero (h : S.Correct) : S.CorrectExcept 0 :=
  (S.correctExcept_iff 0).2 fun κ f x y =>
    (ProbComp.prob_eq_zero_of_allOutputs
      (OracleComp.AllOutputs.mono (fun _ hout hne => hne hout)
        (S.correct_iff.1 h κ f x y))).le

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw
