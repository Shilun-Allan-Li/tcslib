/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Defs
import TCSlib.Cryptography.Encryption.PrivateKey.EnsembleSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Private-key encryption from a pseudorandom generator

An efficient generator evaluator supplies the pad for each challenge message. The security
proof switches each pseudorandom pad to a uniform pad. The two uniform-pad experiments
agree by perfect secrecy.

## Main definitions

* `padXor` masks a message with the first bits of a pad.
* `prgPadFun` and `prgScheme` implement the pad scheme [PS10, Algorithm 92.1].
  The key is an `n`-bit seed, and encryption uses the first `n` bits of the output.

## Main results

* `acceptProb_padXor` proves perfect secrecy for a uniform pad (Claim-92.a).
* `distAdv_padXor_le` bounds the ciphertext advantage by two PRG advantages.
* `prgScheme_encDist` gives the ciphertext sampler's equation.
* `prgScheme_singleMessageSecure` lifts the four-hybrid argument to the asymptotic
  scheme with an efficient generator evaluator [PS10, Theorem 92.2].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.6, Algorithm 92.1 and Theorem 92.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.2–3.3 (the concrete `distAdv`, `prgAdv`, Lemma 3.2).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### The one-time pad with a truncated pad (Claim-92.a) -/

/-- The **truncated one-time pad**: the `n`-bit message `m` masked by the first `n` bits of
the `L`-bit pad `p` (`n ≤ L`), `(m ⊕ p|_n)_i = m_i ⊕ p_i`. With `L = n` this is the one-time
pad; with `p = G(k)` it is the encryption of [PS10, Algorithm 92.1]. -/
def padXor {n L : ℕ} (h : n ≤ L) (m : Fin n → Bool) (p : Fin L → Bool) : Fin n → Bool :=
  fun i => xor (m i) (p (Fin.castLE h i))

/-- The string form of the truncated pad: `List.zipWith xor` of the two encodings (which
truncates to the shorter list) is the encoding of `padXor`. -/
theorem zipWith_xor_ofFn {n L : ℕ} (h : n ≤ L) (m : Fin n → Bool) (p : Fin L → Bool) :
    List.zipWith xor (List.ofFn m) (List.ofFn p) = List.ofFn (padXor h m p) := by
  refine List.ext_getElem (by simp [Nat.min_eq_left h]) fun i h₁ h₂ => ?_
  simp [padXor, Fin.coe_castLE]

/-- **Perfect secrecy of the one-time pad** (Claim-92.a, used in [PS10, Theorems 92.2 and
99.2]): for a uniform pad `p ← U_L` the distributions `m₀ ⊕ p|_n` and `m₁ ⊕ p|_n` are
identical, so every distinguisher accepts them with the same probability.

**Proof sketch.** The map `p ↦ p ⊕ d`, where `d` extends `m₀ ⊕ m₁` by zeros to `L` bits, is
an involution of the pad space with `m₁ ⊕ (p ⊕ d)|_n = m₀ ⊕ p|_n`; relabelling the uniform
pad by it (`acceptProb_comp_equiv`) proves the claim. -/
theorem acceptProb_padXor {ρ : Type*} [Fintype ρ] {n L : ℕ} (h : n ≤ L) (m₀ m₁ : Fin n → Bool)
    (D : (Fin n → Bool) → ρ → Bool) :
    acceptProb (fun p : Fin L → Bool => padXor h m₀ p) D =
      acceptProb (fun p : Fin L → Bool => padXor h m₁ p) D := by
  let d : Fin L → Bool := fun j =>
    if hj : j.val < n then xor (m₀ ⟨j, hj⟩) (m₁ ⟨j, hj⟩) else false
  have hinv : Function.Involutive (fun p : Fin L → Bool => fun j => xor (p j) (d j)) := by
    intro p
    funext j
    show xor (xor (p j) (d j)) (d j) = p j
    cases p j <;> cases d j <;> rfl
  have key : ∀ p : Fin L → Bool, padXor h m₁ (fun j => xor (p j) (d j)) = padXor h m₀ p := by
    intro p
    funext i
    simp only [padXor, d, Fin.coe_castLE, i.isLt, dite_true, Fin.eta]
    cases m₀ i <;> cases m₁ i <;> cases p (Fin.castLE h i) <;> rfl
  calc acceptProb (fun p : Fin L → Bool => padXor h m₀ p) D
      = acceptProb (fun p : Fin L → Bool => padXor h m₁ (hinv.toPerm _ p)) D := by
        congr 1
        funext p
        exact (key p).symm
    _ = acceptProb (fun p : Fin L → Bool => padXor h m₁ p) D :=
        acceptProb_comp_equiv (hinv.toPerm _) (fun p => padXor h m₁ p) D

/-- **The four-hybrid bound of [PS10, Theorem 92.2], concrete:** for a generator
`G : σ → {0,1}^L`, messages `m₀, m₁ ∈ {0,1}^n` (`n ≤ L`) and any distinguisher `D`, the
advantage of `D` between `m₀ ⊕ G(s)|_n` and `m₁ ⊕ G(s)|_n` (`s` uniform) is at most
`prgAdv G (D ∘ (m₀ ⊕ ·)) + prgAdv G (D ∘ (m₁ ⊕ ·))`.

**Proof sketch.** Hybrids `H¹ = m₀ ⊕ G(U)`, `H² = m₀ ⊕ U_L`, `H³ = m₁ ⊕ U_L`, `H⁴ = m₁ ⊕ G(U)`:
`|P(H¹) − P(H²)| = prgAdv G (D ∘ (m₀ ⊕ ·))` and `|P(H³) − P(H⁴)| = prgAdv G (D ∘ (m₁ ⊕ ·))`
are the definitions of `prgAdv` and `distAdv` (the sunglass identity `distAdv_comp`, here
definitional), `P(H²) = P(H³)` is `acceptProb_padXor`, and the triangle inequality
`abs_sub_le` finishes. (The text's "three gaps, `1/(3p(n))`" is this two-term bound.) -/
theorem distAdv_padXor_le {σ ρ : Type*} [Fintype σ] [Fintype ρ] {n L : ℕ} (h : n ≤ L)
    (G : σ → Fin L → Bool) (m₀ m₁ : Fin n → Bool) (D : (Fin n → Bool) → ρ → Bool) :
    distAdv (fun s => padXor h m₀ (G s)) (fun s => padXor h m₁ (G s)) D ≤
      prgAdv G (fun t r => D (padXor h m₀ t) r) + prgAdv G (fun t r => D (padXor h m₁ t) r) := by
  have e := acceptProb_padXor h m₀ m₁ D
  simp only [prgAdv_eq, distAdv_def, acceptProb_def, id_eq] at e ⊢
  rw [← e]
  exact (abs_sub_le _ _ _).trans_eq (congrArg _ (abs_sub_comm _ _))

/-! ### The scheme of [PS10, Algorithm 92.1] -/

/-- The raw string function of `Enc` and `Dec` of [PS10, Algorithm 92.1]: on the machine
layout `⟨⟨⟨1^n, ⟨k, w⟩⟩, α⟩, r⟩` output `w ⊕ F(k)` (bitwise, truncated to the shorter string),
where `F` evaluates the generator. -/
def prgPadFun (F : List Bool → List Bool) (z : List Bool) : List Bool :=
  List.zipWith xor (pairSndD (NUPPT.inArg z)) (F (pairFstD (NUPPT.inArg z)))

/-- `prgPadFun F` is polynomial-time when `F` is: one evaluation of `F` and one bitwise
exclusive-or (`Complexity.polyTimeComputable_pairXor`). -/
theorem polyTimeComputable_prgPadFun {F : List Bool → List Bool} (hF : PolyTimeComputable F) :
    PolyTimeComputable (prgPadFun F) := by
  have h := polyTimeComputable_pairXor.comp
    ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode
      (hF.comp (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)))
  convert h using 1
  funext z
  simp [prgPadFun, Function.comp_apply]

/-- The activation of the pad machine on `⟨k, w⟩` is `w ⊕ F(k)`. -/
theorem runAt_prgPad {F : List Bool → List Bool} (hF : PolyTimeComputable F) (coins : PolyExpr)
    (n : ℕ) (k w : List Bool)
    (r : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prgPadFun hF) coins).Coins n) :
    (NUPPT.ofPolyTimeUniform (polyTimeComputable_prgPadFun hF) coins).runAt n (pairEncode k w) r =
      List.zipWith xor w (F k) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [prgPadFun, NUPPT.inArg_eq, NUPPT.advInput_eq]

/-- The activation of the key generator (the coin string is the key). -/
theorem runAt_coinKey (coins : PolyExpr) (n : ℕ)
    (r : (NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD coins).Coins n) :
    (NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD coins).runAt n [] r = List.ofFn r := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp

/-- Masking twice with the same pad (at least as long as the message) is the identity. -/
private theorem zipWith_xor_xor_self : ∀ (m p : List Bool), m.length ≤ p.length →
    List.zipWith xor (List.zipWith xor m p) p = m
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: m, b :: p, h => by
    simp only [List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨by cases a <;> cases b <;> rfl, zipWith_xor_xor_self m p (by simpa using h)⟩

/-- **The encryption scheme of [PS10, Algorithm 92.1]** for a generator `G` with evaluator
`F`: `Gen(1^n)` outputs a uniform `n`-bit seed `k` (its coin string), `Enc_k(m) = m ⊕ G(k)|_n`
and `Dec_k(c) = c ⊕ G(k)|_n` (`Enc` and `Dec` are deterministic, coins `const 0`). Correctness
is `(m ⊕ p) ⊕ p = m` for a pad `p = G(k)` of length `ℓ(n) > n`.

**Deviation:** the key is an `n`-bit seed and the pad is the first `n` bits of `G(k)` (the
text's `n/2`-bit key for a length-doubling `G` requires `n` even; with syntactic polynomial
lengths (D9) a key length that is a non-constant function of the message length is never
shorter than the message, so the "short key" economy of §3.6 is a matter of parametrization
and the security argument is unchanged); the evaluator `F` of `G` is an explicit argument
rather than extracted from `PRG.Easy`. -/
noncomputable def prgScheme (P : PRG) (F : List Bool → List Bool) (hF : PolyTimeComputable F)
    (hG : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)) : PrivateKeyScheme where
  gen := NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var
  enc := NUPPT.ofPolyTimeUniform (polyTimeComputable_prgPadFun hF) (.const 0)
  dec := NUPPT.ofPolyTimeUniform (polyTimeComputable_prgPadFun hF) (.const 0)
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  correct := by
    intro n m rg re rd
    rw [runAt_coinKey, runAt_prgPad hF, runAt_prgPad hF, hG, zipWith_xor_xor_self, decodeFin_ofFn]
    simp only [List.length_ofFn]
    rw [NUPPT.coinLen_eq, NUPPT.coins_ofPolyTimeUniform]
    exact (P.expands n).le

/-- **The key of Algorithm 92.1 is an `n`-bit seed**: the published equivalence
`(prgScheme P F hF hG).gen.Coins n ≃ {0,1}^n` (`NUPPT.coinsEquiv_ofPolyTimeUniform`). -/
noncomputable def prgScheme_genCoinsEquiv (P : PRG) (F : List Bool → List Bool)
    (hF : PolyTimeComputable F) (hG : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s))
    (n : ℕ) : (prgScheme P F hF hG).gen.Coins n ≃ (Fin n → Bool) :=
  NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n

/-- The key equivalence keeps the coin string. -/
theorem prgScheme_genCoinsEquiv_ofFn (P : PRG) (F : List Bool → List Bool)
    (hF : PolyTimeComputable F) (hG : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s))
    (n : ℕ) (r : (prgScheme P F hF hG).gen.Coins n) :
    List.ofFn (prgScheme_genCoinsEquiv P F hF hG n r) = List.ofFn r :=
  NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn polyTimeComputable_pairSndD .var n r

/-- **The encryptor of Algorithm 92.1 has no coins**: the published equivalence
`(prgScheme P F hF hG).enc.Coins n ≃ {0,1}^0` (`NUPPT.coinsEquiv_ofPolyTimeUniform`). -/
noncomputable def prgScheme_encCoinsEquiv (P : PRG) (F : List Bool → List Bool)
    (hF : PolyTimeComputable F) (hG : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s))
    (n : ℕ) : (prgScheme P F hF hG).enc.Coins n ≃ (Fin 0 → Bool) :=
  NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_prgPadFun hF) (.const 0) n

/-- The encryptor's coin equivalence keeps the (empty) coin string. -/
theorem prgScheme_encCoinsEquiv_ofFn (P : PRG) (F : List Bool → List Bool)
    (hF : PolyTimeComputable F) (hG : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s))
    (n : ℕ) (r : (prgScheme P F hF hG).enc.Coins n) :
    List.ofFn (prgScheme_encCoinsEquiv P F hF hG n r) = List.ofFn r :=
  NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn (polyTimeComputable_prgPadFun hF) (.const 0) n r

/-- **The ciphertext distribution of Algorithm 92.1** is `m ⊕ G(k)|_n` for a uniform seed `k`
(the encryption coins are unused): `encDist n m (k, _) = ofFn (padXor m (G n k))`. -/
theorem prgScheme_encDist (P : PRG) (F : List Bool → List Bool) (hF : PolyTimeComputable F)
    (hG : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)) (n : ℕ)
    (m : Fin n → Bool) (r : (prgScheme P F hF hG).gen.Coins n × (prgScheme P F hF hG).enc.Coins n) :
    (prgScheme P F hF hG).encDist n m r =
      List.ofFn (padXor (P.expands n).le m (P.G n (prgScheme_genCoinsEquiv P F hF hG n r.1))) := by
  rw [PrivateKeyScheme.encDist_apply]
  show (NUPPT.ofPolyTimeUniform (polyTimeComputable_prgPadFun hF) (.const 0)).runAt n
    (pairEncode ((NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var).runAt n [] r.1)
      (List.ofFn m)) r.2 = _
  rw [runAt_coinKey, ← prgScheme_genCoinsEquiv_ofFn P F hF hG n r.1, runAt_prgPad hF, hG]
  exact zipWith_xor_ofFn (P.expands n).le m (P.G n (prgScheme_genCoinsEquiv P F hF hG n r.1))

/-- **Dropping the unused encryption coins of Algorithm 92.1**: the probability that a
distinguisher accepts a ciphertext `encDist n m` of `prgScheme` is the probability that it
accepts the string of `m ⊕ G(s)|_n` for a uniform seed `s`. The seed relabelling
`(s, r) ↦ ((s, ∅), r)` is a bijection because the encryption coin type `Fin 0 → Bool` is a
singleton (`Fin.elim0`); the ciphertext is `prgScheme_encDist`. -/
private theorem acceptProb_prgScheme_encDist (P : PRG) (F : List Bool → List Bool)
    (hF : PolyTimeComputable F) (hG : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s))
    (n : ℕ) (m : Fin n → Bool) {ρ : Type*} [Fintype ρ] (Dst : List Bool → ρ → Bool) :
    acceptProb ((prgScheme P F hF hG).encDist n m) Dst =
      acceptProb (fun s : Fin n → Bool => padXor (P.expands n).le m (P.G n s))
        (fun t r => Dst (List.ofFn t) r) := by
  let e : (Fin n → Bool) × ρ ≃
      ((prgScheme P F hF hG).gen.Coins n × (prgScheme P F hF hG).enc.Coins n) × ρ :=
    { toFun := fun z => (((prgScheme_genCoinsEquiv P F hF hG n).symm z.1,
          (prgScheme_encCoinsEquiv P F hF hG n).symm fun i => Fin.elim0 i), z.2)
      invFun := fun z => (prgScheme_genCoinsEquiv P F hF hG n z.1.1, z.2)
      left_inv := fun z => by simp only [Equiv.apply_symm_apply]
      right_inv := fun z => Prod.ext (Prod.ext (Equiv.symm_apply_apply _ _)
        ((prgScheme_encCoinsEquiv P F hF hG n).injective (by
          rw [Equiv.apply_symm_apply]; exact funext fun i => Fin.elim0 i))) rfl }
  rw [acceptProb_def, acceptProb_def, ← uprob_comp_equiv e]
  congr 1
  funext z
  simp only [e, Equiv.coe_fn_mk, prgScheme_encDist, Equiv.apply_symm_apply]

/-- **A machine that runs `D` on `m ⊕ t` is the distinguisher `D ∘ (m ⊕ ·)`**: if
`B(1^n, t; r) = D(1^n, m ⊕ t|_n; r)` for every `L`-bit string `t` (with `B.coins = D.coins`),
then the PRG advantage of `B` as a typed distinguisher of `L`-bit strings equals the PRG
advantage of `D ∘ (m ⊕ ·)` — the machine form of the hybrid distinguishers of
[PS10, Theorem 92.2, proof] (`PrivateKeyScheme.acceptProb_distinguisherL_congr` on both terms of `prgAdv`). -/
private theorem prgAdv_eq_of_runAtL {n L : ℕ} (h : n ≤ L) {B D : NUPPT} (hc : B.coins = D.coins)
    (m : Fin n → Bool) {σ : Type*} [Fintype σ] (G : σ → Fin L → Bool)
    (hB : ∀ (t : Fin L → Bool) r,
      B.runAtL n (List.ofFn t) r = D.runAtL n (List.ofFn (padXor h m t)) r) :
    prgAdv G (fun t r => D.distinguisherL n (List.ofFn (padXor h m t)) r) =
      prgAdv G (B.distinguisher n L) := by
  simp only [prgAdv_eq, distAdv_def]
  have e₁ : acceptProb G (B.distinguisher n L) =
      acceptProb (fun s => List.ofFn (G s)) (B.distinguisherL n) := by
    simp only [acceptProb_def, NUPPT.distinguisher_eq]
  have e₂ : acceptProb id (B.distinguisher n L) =
      acceptProb (fun t : Fin L → Bool => List.ofFn t) (B.distinguisherL n) := by
    simp only [acceptProb_def, NUPPT.distinguisher_eq, id_eq]
  rw [e₁, e₂,
    PrivateKeyScheme.acceptProb_distinguisherL_congr hc n _ (fun s => List.ofFn (padXor h m (G s)))
      (fun s r => hB (G s) r),
    PrivateKeyScheme.acceptProb_distinguisherL_congr hc n _ (fun t => List.ofFn (padXor h m t)) (fun t r => hB t r)]
  simp only [acceptProb_def, id_eq]

/-- **[PS10, Theorem 92.2]: the scheme of Algorithm 92.1 is single-message secure** when `G`
is a pseudorandom generator.

**Proof sketch.** Fix a non-uniform PPT `D`. At each `n` choose a pair `(m₀ⁿ, m₁ⁿ)`
maximizing `distAdv (encDist n m₀) (encDist n m₁) (D.distinguisherL n)` over the finite
message space (`Finset.exists_max_image`; the text's footnote: "`Mᵢ` is non-uniform as it has
the message hard-coded"). Concrete step: by `prgScheme_encDist` the sampler `encDist n mᵢ`
is `(k, _) ↦ ofFn (padXor mᵢ (G n k))`; drop the unused encryption coins (the coin type
`Fin 0 → Bool` is a singleton) and move `List.ofFn` into the distinguisher
(`acceptProb_prgScheme_encDist`), and apply `distAdv_padXor_le`: the advantage at `n` is at most
`prgAdv (G n) D₀ⁿ + prgAdv (G n) D₁ⁿ` with `Dᵢⁿ t r := D.distinguisherL n (ofFn (padXor mᵢⁿ t)) r`
— the four hybrids `H¹ = m₀ ⊕ G(U_n)`, `H² = m₀ ⊕ U_ℓ`, `H³ = m₁ ⊕ U_ℓ`, `H⁴ = m₁ ⊕ G(U_n)` of
the text. Machine step: for `i = 0, 1` the machine `Bᵢ` has advice `⟨ofFn mᵢⁿ, D.advice n⟩`
(`NUPPT.exists_withAdvice` with the bound `var`), coins `D.coins`, and on `⟨1^n, t⟩` computes
`zipWith xor (ofFn mᵢⁿ) t` (`Complexity.polyTimeComputable_pairXor`; equal to
`ofFn (padXor mᵢⁿ t)` by `zipWith_xor_ofFn`) and runs `D` on it (`NUPPT.exists_comp`), so
`prgAdv (G n) Dᵢⁿ = prgAdv (G n) (Bᵢ.distinguisher n (ℓ n))` after transporting the coins
along `Bᵢ.coins = D.coins` (`prgAdv_eq_of_runAtL`, `PrivateKeyScheme.acceptProb_distinguisherL_congr`).
Asymptotic step:
`ν n := prgAdv (G n) (B₀.distinguisher n (ℓ n)) + prgAdv (G n) (B₁.distinguisher n (ℓ n))` is
negligible by `PRG.secure_iff` applied to `hP` and `Negligible.add`; by maximality
`distAdv (encDist n m₀) (encDist n m₁) (D.distinguisherL n) ≤ ν n` for every `n, m₀, m₁`, so
`ε := ν` witnesses `SingleMessageSecure`. -/
theorem prgScheme_singleMessageSecure (P : PRG) (hP : P.Secure) (F : List Bool → List Bool)
    (hF : PolyTimeComputable F) (hG : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)) :
    (prgScheme P F hF hG).SingleMessageSecure := by
  apply (PrivateKeyScheme.singleMessageSecure_iff _).2
  intro D
  -- the worst message pair at each parameter (hard-wired into the reductions)
  have hmax : ∀ n, ∃ p : (Fin n → Bool) × (Fin n → Bool), ∀ q : (Fin n → Bool) × (Fin n → Bool),
      distAdv ((prgScheme P F hF hG).encDist n q.1) ((prgScheme P F hF hG).encDist n q.2)
          (D.distinguisherL n) ≤
        distAdv ((prgScheme P F hF hG).encDist n p.1) ((prgScheme P F hF hG).encDist n p.2)
          (D.distinguisherL n) := by
    intro n
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
      (fun q : (Fin n → Bool) × (Fin n → Bool) =>
        distAdv ((prgScheme P F hF hG).encDist n q.1) ((prgScheme P F hF hG).encDist n q.2)
          (D.distinguisherL n)) Finset.univ_nonempty
    exact ⟨p, fun q => hp q (Finset.mem_univ q)⟩
  choose μ hμ using hmax
  -- the reductions `Bᵢ`: mask the challenge with the hard-wired message, then run `D`
  have hpre : PolyTimeComputable fun z => List.zipWith xor (pairSndD z) (pairFstD z) := by
    have := polyTimeComputable_pairXor.comp
      (polyTimeComputable_pairSndD.pairEncode polyTimeComputable_pairFstD)
    convert this using 1
    funext z
    simp [Function.comp_apply]
  obtain ⟨D', hD'c, -, -, hD'⟩ := D.exists_comp hpre polyTimeComputable_id
  obtain ⟨B₀, hB₀c, hB₀⟩ := D'.exists_withAdvice (fun n => List.ofFn (μ n).1) .var (fun n => by simp)
  obtain ⟨B₁, hB₁c, hB₁⟩ := D'.exists_withAdvice (fun n => List.ofFn (μ n).2) .var (fun n => by simp)
  have hrun : ∀ (B : NUPPT) (β : ∀ n, Fin n → Bool),
      (∀ n y r, B.runAtL n y r = D'.runAtL n (pairEncode y (List.ofFn (β n))) r) →
      ∀ n (t : Fin (P.stretch.eval n) → Bool) r,
        B.runAtL n (List.ofFn t) r = D.runAtL n (List.ofFn (padXor (P.expands n).le (β n) t)) r := by
    intro B β hB n t r
    rw [hB, hD', pairSndD_pairEncode, pairFstD_pairEncode, zipWith_xor_ofFn]
    rfl
  -- the negligible bound: the two PRG advantages of `B₀`, `B₁`
  refine ⟨fun n => prgAdv (P.G n) (B₀.distinguisher n (P.stretch.eval n)) +
    prgAdv (P.G n) (B₁.distinguisher n (P.stretch.eval n)),
    (((PRG.secure_iff P).1 hP).2 B₀).add (((PRG.secure_iff P).1 hP).2 B₁),
    fun n m₀ m₁ => ?_⟩
  refine (hμ n (m₀, m₁)).trans ?_
  simp only [distAdv_def]
  rw [acceptProb_prgScheme_encDist, acceptProb_prgScheme_encDist,
    ← prgAdv_eq_of_runAtL (P.expands n).le (hB₀c.trans hD'c) (μ n).1 (P.G n) (hrun B₀ _ hB₀ n),
    ← prgAdv_eq_of_runAtL (P.expands n).le (hB₁c.trans hD'c) (μ n).2 (P.G n) (hrun B₁ _ hB₁ n)]
  exact (distAdv_def _ _ _).symm.trans_le (distAdv_padXor_le (P.expands n).le (P.G n) (μ n).1
    (μ n).2 (fun t r => D.distinguisherL n (List.ofFn t) r))

end TCSlib.Cryptography
