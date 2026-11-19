/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Bootstrap
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Security

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Weak circular security of public-key GSW (concrete, per distinguisher)

## Main definitions

* `FheView`, `Seeds`: reducible names for the FHE view `(pk, evk, ct)` and its seed type.
* `fheView`: the FHE view of a bit from honest key generation, the evaluation key of P6-Q8 and
  one public-key encryption.
* `WeakCircularSecure P χ D ε`: one distinguisher `D` has advantage at most `ε` between the
  FHE views of `0` and `1`; with its reader `weakCircularSecure_iff`.

## Main results

* `distAdv_fheView_noEvk_le` (G15): with the evaluation key dropped, the view inherits phase
  5's IND-CPA bound `distAdv_encrypt_le` (two DLWE advantages plus `2·N·ε_LHL`).

Ruling Q-6B-1 A: r3's G14 (`distAdv_fheView_le`) is not a theorem. The reader
`weakCircularSecure_iff` is that statement: under the hypothesis `WeakCircularSecure P χ D ε`
the advantage on the FHE views is at most `ε`. It is the security half of [BV11, Thm 3.2] and
[BV14, Thm 2.14 second part]: pure-FHE security *is* the hypothesis (A1).

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: §2.5, Thm 2.14.
* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from
  (Standard) LWE*, FOCS 2011 full version; IACR ePrint 2011/344: Def 3.1, Thm 3.2, Def 3.8.
* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; IACR ePrint 2013/340, version dated
  8 June 2013: §3.2.
* [AP14] J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*,
  CRYPTO 2014; IACR ePrint 2014/094: §5.3.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, §6.1.2 (circular security).

**Deviations.** [BV11, Def 3.8] is asymptotic; `WeakCircularSecure` is its concrete form for
one distinguisher (P6-Q15 A), and the asymptotic `WeakCircularSecureFamily`
(`GSW/Asymptotic.lean`) is the headline hypothesis. Weak circular security is an explicit
hypothesis (A1), never derived from LWE: its truth for GSW is open [Pei16, §6.1.2].
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open Encryption.PublicKey

/-- The FHE view `(pk, evk, ct)`: a public key, the `N` evaluation-key ciphertexts and one
challenge ciphertext. Reducible notation. -/
abbrev FheView (P : Parameters) : Type :=
  PublicKey P × (Fin P.columns → Ciphertext P) × Ciphertext P

/-- `FheView P` is `PublicKey P × (Fin P.columns → Ciphertext P) × Ciphertext P`. -/
theorem FheView_eq (P : Parameters) :
    FheView P = (PublicKey P × (Fin P.columns → Ciphertext P) × Ciphertext P) := rfl

/-- The seeds of the FHE view: a key-generation seed, the coins of the `N` evaluation-key
encryptions and the coins of the challenge encryption. Reducible notation. -/
abbrev Seeds (P : Parameters) (χ : LWE.Noise) : Type :=
  KeySeed P χ × (Fin P.columns → Coins P) × Coins P

/-- `Seeds P χ` is `KeySeed P χ × (Fin P.columns → Coins P) × Coins P`. -/
theorem Seeds_eq (P : Parameters) (χ : LWE.Noise) :
    Seeds P χ = (KeySeed P χ × (Fin P.columns → Coins P) × Coins P) := rfl

/-- **The FHE view of a bit** `μ` [BV14, §2.5, p007-b001: "the adversary is given both pk and
evk"; BV11, Def 3.1, p013-b002]: from a seed `r = (rg, R, R₀)`, honest key generation
`(pk, s) = Regev.keygen P.lwe χ rg`, the evaluation key `evalKey P pk s R` (P6-Q8) and the
challenge `encrypt P pk μ R₀`:
`fheView P χ μ r = (pk, evalKey P pk s r.2.1, encrypt P pk μ r.2.2)`. -/
@[simps! (config := { isSimp := false }) fst snd]
def fheView (P : Parameters) (χ : LWE.Noise) (μ : Bool) (r : Seeds P χ) : FheView P :=
  ((Regev.keygen P.lwe χ r.1).1,
    evalKey P (Regev.keygen P.lwe χ r.1).1 (Regev.keygen P.lwe χ r.1).2 r.2.1,
    encrypt P (Regev.keygen P.lwe χ r.1).1 μ r.2.2)

/-- `fheView P χ μ r` is `(pk, evalKey P pk s r.2.1, encrypt P pk μ r.2.2)` with
`(pk, s) = Regev.keygen P.lwe χ r.1`. -/
theorem fheView_eq (P : Parameters) (χ : LWE.Noise) (μ : Bool) (r : Seeds P χ) :
    fheView P χ μ r =
      ((Regev.keygen P.lwe χ r.1).1,
        evalKey P (Regev.keygen P.lwe χ r.1).1 (Regev.keygen P.lwe χ r.1).2 r.2.1,
        encrypt P (Regev.keygen P.lwe χ r.1).1 μ r.2.2) := rfl

/-- **Weak circular security, concrete, for one distinguisher** (P6-Q15 A) [BV11, Def 3.8,
p015-b001; BV14, Thm 2.14, p008-b003; Pei16, §6.1.2, p068-b001]: the distinguisher `D`, with
coins in `ρ`, has advantage at most `ε` between the FHE views of `0` and `1`,
`WeakCircularSecure P χ D ε ↔ distAdv (fheView P χ false) (fheView P χ true) D ≤ ε`. A
hypothesis (A1), never derived from LWE (phase-5 Q15). Its reader `weakCircularSecure_iff` is
the security half of [BV11, Thm 3.2, p015-b001] and [BV14, Thm 2.14 second part, p008-b003]
(ruling Q-6B-1 A: r3's G14). Deviation: BV11's definition is asymptotic, and
`WeakCircularSecureFamily` is the headline form. It is stated per distinguisher because, for
parameters under which decryption is correct, quantified over **every** function
`FheView P → ρ → Bool` it would hold only for `ε` near `1`: an unbounded test can enumerate the
key-generation seeds, take any seed whose public key is `pk`, and decrypt the challenge with
that seed's secret. Recovering the original `s` uniquely is unnecessary. The definition also
admits parameters that do not decrypt correctly, to which this argument does not apply. -/
def WeakCircularSecure (P : Parameters) (χ : LWE.Noise) {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (D : FheView P → ρ → Bool) (ε : ℝ) : Prop :=
  distAdv (fheView P χ false) (fheView P χ true) D ≤ ε

/-- `WeakCircularSecure P χ D ε` holds exactly when
`distAdv (fheView P χ false) (fheView P χ true) D ≤ ε`. This reader is r3's G14 (Q-6B-1 A). -/
theorem weakCircularSecure_iff (P : Parameters) (χ : LWE.Noise) {ρ : Type*} [Fintype ρ]
    [Nonempty ρ] (D : FheView P → ρ → Bool) (ε : ℝ) :
    WeakCircularSecure P χ D ε ↔ distAdv (fheView P χ false) (fheView P χ true) D ≤ ε :=
  Iff.rfl

/-! ### Target G15 -/

/-- **G15. Without the evaluation key, the FHE view is phase 5's.** For every distinguisher
`D` of `(pk, ct)` pairs and all bits `μ₀`, `μ₁`, the views `(pk, encrypt pk μ R₀)` read off
`fheView`'s seeds (the evaluation key dropped) differ by at most two DLWE advantages plus
`2·(N·ε_LHL)`, phase 5's bound:
`distAdv (fun r => ((fheView P χ μ₀ r).1, (fheView P χ μ₀ r).2.2))
(fun r => ((fheView P χ μ₁ r).1, (fheView P χ μ₁ r).2.2)) D ≤
decisionAdvantage P.lwe χ (reduction P μ₀ D) + decisionAdvantage P.lwe χ (reduction P μ₁ D) +
2 * (P.columns * Regev.extractionError P.lwe)` [GSW13, §3.2, p009-b002; AP14, §5.3,
p015-b002]. Stated over the projection of `fheView`, not over `realView`, of which it would be
a restatement (G45-01); its content is the transport of `distAdv_encrypt_le` along the coin
regrouping.

**Proof sketch.** Through `fheView_fst`, `fheView_snd` (or `fheView_eq`), `Regev.keygen_fst`
and `realView_eq`, `view_eq`, the projected view at a seed `(rg, R, R₀)` is
`realView P χ μ (rg, R₀)`: it does not read the evaluation-key coins `R`. Through
`acceptProb_def` and `acceptProb_comp_equiv`, regroup the seed-and-coin space so that the
unused coins `R` form the second factor, `((KeySeed P χ × Coins P) × ρ) × (Fin N → Coins P)`
(`Equiv.prodComm`, `Equiv.prodAssoc`); the marginalization lemma `uprob_fst`
(`Foundations/Probability.lean`) then drops that factor, so each `acceptProb` equals that of
`realView P χ μ`. Then `distAdv_def` and phase 5's `distAdv_encrypt_le`. -/
theorem distAdv_fheView_noEvk_le (P : Parameters) (χ : LWE.Noise) {ρ : Type*} [Fintype ρ]
    [Nonempty ρ] (μ₀ μ₁ : Bool) (D : PublicKey P × Ciphertext P → ρ → Bool) :
    distAdv (fun r : Seeds P χ => ((fheView P χ μ₀ r).1, (fheView P χ μ₀ r).2.2))
        (fun r : Seeds P χ => ((fheView P χ μ₁ r).1, (fheView P χ μ₁ r).2.2)) D ≤
      LWE.decisionAdvantage P.lwe χ (reduction P μ₀ D) +
        LWE.decisionAdvantage P.lwe χ (reduction P μ₁ D) +
        2 * (P.columns * Regev.extractionError P.lwe) := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

set_option pp.fullNames true
set_option pp.funBinderTypes true
#check @TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.distAdv_fheView_noEvk_le
