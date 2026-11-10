/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreLoops
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.Hybrid
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Multi-message secure encryption from a pseudorandom function

The key generator samples a key. The encryptor samples an independent point, masks the
message with the function value at that point, and returns the point with the masked message.
Decryption recomputes the mask and checks the ciphertext format [PS10, Algorithm 99.1].

## Main definitions

* `prfEncFun`, `prfDecFun` and `prfScheme` implement the scheme from a polynomial-time evaluator.
* `encodeTuple` encodes the fixed vector of ciphertext pairs as a string.

## Main results

* `prfScheme_multiEncDist` identifies the ciphertext sampler with the encoded real hybrid.
* `prfScheme_multiMessageSecure` lifts the six-hybrid bound to a negligible advantage against
  non-uniform polynomial-time distinguishers [PS10, Theorem 99.2].
* `exists_multiMessageSecure_of_prf` and `exists_multiMessageSecure_of_exists_prg` give the
  existence results from a PRF and, via GGM, from a PRG.

## Contents

* `FromPRF.Hybrid` proves the concrete six-hybrid bound.
* `FromPRF.HybridLemmas` supplies the collision and coin-relabelling estimates.
* `FromPRF.ReductionMachine` implements the next-query reduction and proves its run agreement.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.7, Definition 93.1, and §3.9, Algorithm 99.1 and Theorem 99.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (oracle adversaries and PRF advantage).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### The scheme of [PS10, Algorithm 99.1] -/

/-- The raw string function of `Enc` of [PS10, Algorithm 99.1]: on the machine layout
`⟨⟨⟨1^n, ⟨k, w⟩⟩, α⟩, r⟩` output the pair `⟨r, w ⊕ E(⟨k, r⟩)⟩`, where `E` evaluates the PRF on
`⟨key, input⟩` and the coin string `r` is the fresh point. -/
def prfEncFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode (NUPPT.inCoins z)
    (List.zipWith xor (pairSndD (NUPPT.inArg z))
      (E (pairEncode (pairFstD (NUPPT.inArg z)) (NUPPT.inCoins z))))

/-- Whether the ciphertext `⟨r, c⟩` of the layout `⟨⟨⟨1^n, ⟨k, ⟨r, c⟩⟩⟩, α⟩, r'⟩` has `n`-bit
components: the domain of `Dec` in [PS10, Algorithm 99.1]. -/
def prfDecWF (z : List Bool) : Bool :=
  decide ((pairFstD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length) &&
    decide ((pairSndD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length)

/-- The raw string function of `Dec` of [PS10, Algorithm 99.1]: on the layout
`⟨⟨⟨1^n, ⟨k, ⟨r, c⟩⟩⟩, α⟩, r'⟩` with `n`-bit `r` and `c`, output `c ⊕ E(⟨k, r⟩)`; on any other
ciphertext, output `⊥`, here the `(n + 1)`-bit string `1^{n+1}`, which decodes to no message.

The source defines `Dec` on pairs of `n`-bit strings only. The guard matters under
chosen-ciphertext attacks: `E` agrees with `F` only on `⟨s, x⟩` with `|s| = |x|`, so without it a
malformed ciphertext would evaluate `E` where it is unconstrained, and there it may reveal the
key. -/
def prfDecFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  if prfDecWF z then
    List.zipWith xor (pairSndD (pairSndD (NUPPT.inArg z)))
      (E (pairEncode (pairFstD (NUPPT.inArg z)) (pairFstD (pairSndD (NUPPT.inArg z)))))
  else true :: NUPPT.inParam z

/-- `prfEncFun E` is polynomial-time when `E` is: projections, one evaluation of `E`, one
bitwise exclusive-or (`Complexity.polyTimeComputable_pairXor`) and one pairing. -/
theorem polyTimeComputable_prfEncFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (prfEncFun E) := by
  have h := NUPPT.polyTimeComputable_inCoins.pairEncode
    (polyTimeComputable_pairXor.comp
      ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode
        (hE.comp ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
          NUPPT.polyTimeComputable_inCoins))))
  convert h using 1
  funext z
  simp [prfEncFun, Function.comp_apply]

/-- The well-formedness test of `Dec` is polynomial-time: two length comparisons
(`Complexity.polyTimeComputable_lenEq`). -/
theorem polyTimeComputable_prfDecWF : PolyTimeComputable (fun z => [prfDecWF z]) := by
  have hl : ∀ g : List Bool → List Bool, PolyTimeComputable g →
      PolyTimeComputable (fun z => [decide ((g z).length = (NUPPT.inParam z).length)]) := by
    intro g hg
    convert polyTimeComputable_lenEq.comp (hg.pairEncode NUPPT.polyTimeComputable_inParam)
      using 1
    funext z
    simp [Function.comp_apply]
  exact polyTimeComputable_and
    (hl _ ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
      NUPPT.polyTimeComputable_inArg))
    (hl _ ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp
      NUPPT.polyTimeComputable_inArg))

/-- `prfDecFun E` is polynomial-time when `E` is: the guard, then the branch of the old `Dec`
(`Complexity.polyTimeComputable_ite`). -/
theorem polyTimeComputable_prfDecFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (prfDecFun E) := by
  refine polyTimeComputable_ite polyTimeComputable_prfDecWF ?_
    ((polyTimeComputable_const [true]).append NUPPT.polyTimeComputable_inParam)
  have h := polyTimeComputable_pairXor.comp
    (((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp
        NUPPT.polyTimeComputable_inArg).pairEncode
      (hE.comp ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
        ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
          NUPPT.polyTimeComputable_inArg))))
  convert h using 1
  funext z
  simp [prfDecFun, Function.comp_apply]

/-- The activation of the encryption machine on `⟨k, w⟩` with coins `r` is
`⟨r, w ⊕ E(⟨k, r⟩)⟩`. -/
theorem runAt_prfEnc {E : List Bool → List Bool} (hE : PolyTimeComputable E) (coins : PolyExpr)
    (n : ℕ) (k w : List Bool)
    (r : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) coins).Coins n) :
    (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) coins).runAt n (pairEncode k w) r =
      pairEncode (List.ofFn r) (List.zipWith xor w (E (pairEncode k (List.ofFn r)))) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [prfEncFun, NUPPT.inArg_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq]

/-- The activation of the decryption machine on `⟨k, ⟨r, c⟩⟩` with `n`-bit `r` and `c` is
`c ⊕ E(⟨k, r⟩)`. -/
theorem runAt_prfDec {E : List Bool → List Bool} (hE : PolyTimeComputable E) (coins : PolyExpr)
    (n : ℕ) (k r c : List Bool) (hr : r.length = n) (hc : c.length = n)
    (r' : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).Coins n) :
    (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).runAt n
        (pairEncode k (pairEncode r c)) r' =
      List.zipWith xor c (E (pairEncode k r)) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [prfDecFun, prfDecWF, NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq, hr, hc]

/-- On a ciphertext `w` whose two projections `pairFstD w` and `pairSndD w` are not both `n` bits
long, the decryption machine outputs `⊥`: a string that decodes to no `n`-bit message. -/
theorem decodeFin_runAt_prfDec_of_not_wf {E : List Bool → List Bool} (hE : PolyTimeComputable E)
    (coins : PolyExpr) (n : ℕ) (k w : List Bool)
    (hw : ¬ ((pairFstD w).length = n ∧ (pairSndD w).length = n))
    (r' : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).Coins n) :
    decodeFin n ((NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).runAt n
        (pairEncode k w) r') = none := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  have hf : prfDecWF (pairEncode (pairEncode (NUPPT.advInput n (pairEncode k w)) [])
      (List.ofFn r')) = false := by
    simp only [prfDecWF, NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq, pairFstD_pairEncode,
      pairSndD_pairEncode, List.length_replicate, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    tauto
  rw [prfDecFun, hf]
  simp [decodeFin_eq, NUPPT.inParam_eq, NUPPT.advInput_eq]

/-- Masking twice with the same pad (at least as long as the message) is the identity
(private copy of the helper of `Asymptotic/Encryption.lean`). -/
private theorem zipWith_xor_xor_self : ∀ (m p : List Bool), m.length ≤ p.length →
    List.zipWith xor (List.zipWith xor m p) p = m
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: m, b :: p, h => by
    simp only [List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨by cases a <;> cases b <;> rfl, zipWith_xor_xor_self m p (by simpa using h)⟩

/-- **The many-message encryption scheme of [PS10, Algorithm 99.1]** for a function family
`F` with polynomial-time evaluator `E` on `⟨s, x⟩`: `Gen(1^n)` outputs a uniform `n`-bit key
`k` (its coin string); `Enc_k(m)` draws `r ← U_n` (its coin string) and outputs
`⟨r, m ⊕ f_k(r)⟩`; `Dec_k(⟨r, c⟩) = c ⊕ f_k(r)` (deterministic, coins `const 0`). Correctness is
`(m ⊕ p) ⊕ p = m` with the `n`-bit pad `p = f_k(r)`.

**Deviation:** `prfScheme`: the key is the `n`-bit coin string of `Gen`; `Enc` draws its `n`-bit
`r` as its coin string; the evaluator `E` of the PRF is an explicit argument rather than
extracted from `PRF.easy`; ciphertexts are the pair `⟨r, m ⊕ f_k(r)⟩`. -/
noncomputable def prfScheme (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)) :
    PrivateKeyScheme where
  gen := NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var
  enc := NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var
  dec := NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) (.const 0)
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  correct := by
    intro n m rg re rd
    rw [runAt_coinKey, runAt_prfEnc hE]
    have h : E (pairEncode (List.ofFn rg) (List.ofFn re)) =
        List.ofFn (F n (NUPPT.coinsEquiv_ofPolyTimeUniform _ _ n rg)
          (NUPPT.coinsEquiv_ofPolyTimeUniform _ _ n re)) := by
      rw [← hFE, NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn]
    have hre : (List.ofFn re).length = n := by
      rw [← NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n re, List.length_ofFn, PolyExpr.eval_var]
    rw [h, runAt_prfDec hE _ _ _ _ _ hre (by simp), h,
      zipWith_xor_xor_self _ _ (by simp), decodeFin_ofFn]

/-- The key generator of `prfScheme` is the uniform machine returning its coin string
[PS10, Algorithm 99.1]. -/
theorem prfScheme_gen (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    (prfScheme F E hE hFE).gen = NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var := rfl

/-- The encryptor of `prfScheme` uses its raw encryption function and `n` coins
[PS10, Algorithm 99.1]. -/
theorem prfScheme_enc (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    (prfScheme F E hE hFE).enc =
      NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var := rfl

/-- The encoding of a tuple of ciphertext pairs `(r_j, c_j)_j` as the string handed to a
distinguisher: `encodeList` of the pairs `⟨r_j, c_j⟩`. -/
def encodeTuple {n q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) : List Bool :=
  PrivateKeyScheme.encodeList (List.ofFn fun j => pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2))

/-- `encodeList l` is the concatenation of the self-delimited chunks `⟨c, []⟩`, `c ∈ l`. -/
private theorem encodeList_eq_flatMap : ∀ l : List (List Bool),
    PrivateKeyScheme.encodeList l = l.flatMap fun c => pairEncode c []
  | [] => by rw [PrivateKeyScheme.encodeList_nil, List.flatMap_nil]
  | c :: l => by
    rw [PrivateKeyScheme.encodeList_cons, List.flatMap_cons, encodeList_eq_flatMap l]
    simp [pairEncode_eq]

/-- The encoded ciphertext tuple is the concatenation of the chunks `⟨⟨r_j, c_j⟩, []⟩` (the
form in which the next-query machine of `MultiMsg.exists_queryChain_nuppt` produces it). -/
theorem encodeTuple_eq_flatten {n q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :
    encodeTuple v =
      (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) []).flatten := by
  rw [encodeTuple, encodeList_eq_flatMap, MultiMsg.flatMap_ofFn]

/-- **The coins of the multi-message experiment of Algorithm 99.1 are bit strings**: the key
coins of `Gen` and the `q + 1` coin strings of `Enc` are `n`-bit strings,
`gen.Coins n × (Fin (q + 1) → enc.Coins n) ≃ {0,1}^n × ({0,1}^n)^{q+1}` (the published coin
identifications `NUPPT.coinsEquiv_ofPolyTimeUniform`; they keep every coin string). -/
noncomputable def prfScheme_coinsEquiv (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x))
    (n q : ℕ) :
    (prfScheme F E hE hFE).gen.Coins n × (Fin (q + 1) → (prfScheme F E hE hFE).enc.Coins n) ≃
      (Fin n → Bool) × (Fin (q + 1) → Fin n → Bool) :=
  (NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n).prodCongr
    (Equiv.piCongrRight fun _ =>
      NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var n)

/-- The coin equivalence of the multi-message experiment keeps every coin string: the key,
`List.ofFn (prfScheme_coinsEquiv … r).1 = List.ofFn r.1`, and each point,
`List.ofFn ((prfScheme_coinsEquiv … r).2 j) = List.ofFn (r.2 j)`. -/
theorem prfScheme_coinsEquiv_ofFn (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x))
    (n q : ℕ)
    (r : (prfScheme F E hE hFE).gen.Coins n × (Fin (q + 1) → (prfScheme F E hE hFE).enc.Coins n)) :
    List.ofFn (prfScheme_coinsEquiv F E hE hFE n q r).1 = List.ofFn r.1 ∧
      ∀ j, List.ofFn ((prfScheme_coinsEquiv F E hE hFE n q r).2 j) = List.ofFn (r.2 j) :=
  ⟨NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n r.1,
    fun j => NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n (r.2 j)⟩

/-- **The ciphertext tuple of Algorithm 99.1** is the encoding of the hybrid `H¹`: for the key
`k` and the points `r_j` read off the coins `r` (`prfScheme_coinsEquiv`),
`multiEncDist n q m r = encodeTuple (prfEncReal (F n) m (prfScheme_coinsEquiv … r))`.

**Proof sketch.** `multiEncDist_apply` writes the left side as `encodeList` of the encryptions
`Enc_k(m_j; r_j)`; the key machine outputs its coin string (`runAt_coinKey`) and the encryption
machine outputs `⟨r_j, m_j ⊕ E(⟨k, r_j⟩)⟩` (`runAt_prfEnc`). The coin strings are those of
`prfScheme_coinsEquiv … r` (`prfScheme_coinsEquiv_ofFn`), so `hFE` turns `E(⟨k, r_j⟩)` into
`F n k r_j` and `zipWith_xor_ofFn_add` gives the `j`-th pair of `prfEncReal`. -/
theorem prfScheme_multiEncDist (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x))
    (n q : ℕ) (m : Fin (q + 1) → Fin n → Bool)
    (r : (prfScheme F E hE hFE).gen.Coins n × (Fin (q + 1) → (prfScheme F E hE hFE).enc.Coins n)) :
    (prfScheme F E hE hFE).multiEncDist n q m r =
      encodeTuple (prfEncReal (F n) m (prfScheme_coinsEquiv F E hE hFE n q r)) := by
  rw [PrivateKeyScheme.multiEncDist_apply, encodeTuple]
  congr 1
  congr 1
  funext j
  show (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var).runAt n
    (pairEncode ((NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var).runAt n [] r.1)
      (List.ofFn (m j))) (r.2 j) = _
  rw [runAt_coinKey, runAt_prfEnc hE]
  have h1 : List.ofFn r.1 = List.ofFn (prfScheme_coinsEquiv F E hE hFE n q r).1 :=
    (prfScheme_coinsEquiv_ofFn F E hE hFE n q r).1.symm
  have h2 : List.ofFn (r.2 j) = List.ofFn ((prfScheme_coinsEquiv F E hE hFE n q r).2 j) :=
    ((prfScheme_coinsEquiv_ofFn F E hE hFE n q r).2 j).symm
  rw [h1, h2, hFE, zipWith_xor_ofFn_add, prfEncReal_apply]

/-- **[PS10, Theorem 99.2]: the scheme of Algorithm 99.1 is multi-message secure** when `F` is
a pseudorandom function family.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** Fix a non-uniform PPT `D` and a budget polynomial `q`. At each `n` choose a
pair of message vectors `(mⁿ, m'ⁿ)` maximizing
`distAdv (multiEncDist n (q n) m) (multiEncDist n (q n) m') (D.distinguisherL n)` over the finite
type of pairs (`Finset.exists_max_image`; the text: "there exists messages `m̄`, `m̄'` … for
infinitely many `n`", hard-wired as advice). *Concrete step:* by `prfScheme_multiEncDist` both
samplers are `encodeTuple ∘ prfEncReal (F n) mⁿ` resp. `m'ⁿ` on the seed space
`K × (Fin (q n + 1) → {0,1}^n)` (the gen coins are the `n`-bit key and the enc coins the points,
definitionally), so with `Dⁿ v c := D.distinguisherL n (encodeTuple v) c` the sunglass identity
`distAdv_comp` and `distAdv_prfEncReal_le` bound the advantage at `n` by
`prfAdv (F n) (multiMsgAdv mⁿ Dⁿ) + prfAdv (F n) (multiMsgAdv m'ⁿ Dⁿ) + 2 · C(q n + 1, 2) / 2^n`
— the six hybrids `H¹, …, H⁶` of the text. *Machine step* (Thm-99.2.1 as an `NUPPT`): for
`v ∈ {m, m'}` the next-query machine `B_v` has advice `⟨encodeList (ofFn (ofFn ∘ vⁿ)), D.advice n⟩`
(`NUPPT.exists_withAdvice`, bound `.add (.mul (.add q (.const 1)) (.add (.mul (.const 2) .var) (.const 2))) D.adv`-style),
coins `(q + 1) · var + D.coins` (`NUPPT.exists_split` with `p := .mul (.add q (.const 1)) .var`: the
first `(q n + 1) n` coins are the points `r₀ … r_{q n}`, read as blocks by
`Complexity.polyTimeComputable_blockMap .var`), and on the encoded history `hist` outputs: if
`|hist| ≤ q n` the query `⟨[false], r_{|hist|}⟩` (history length by `polyTimeComputable_blockMap`
counting, `pairDecode`/`decodeFin` are FP), else the verdict `[true, b]` where `b` is `D`'s
verdict on `encodeTuple (r_j, v_j ⊕ ans_j)_j` (`polyTimeComputable_pairXor` blockwise,
`NUPPT.exists_comp`). By induction on the history, `buildTree` with budget `q n + 1` from `[]`
is the chain `chainTree (q n + 1) r (…)`, i.e.
`B_v.toOracleAdversary n n n (q n + 1) = multiMsgAdv vⁿ Dⁿ` up to the coin bijection
`B_v.Coins n ≃ (Fin (q n + 1) → {0,1}^n) × D.Coins n` (`FunFamily.blocks`, `Fin.appendEquiv`),
so `acceptProb_comp_equiv` gives `prfAdv (F n) (B_v^{(q n + 1)}) = prfAdv (F n) (multiMsgAdv vⁿ Dⁿ)`.
*Asymptotic step:* `hF.negligible_prfAdv B_v (.add q (.const 1))` makes both PRF terms
negligible; the collision term is negligible by `negligible_two_pow_neg` and
`Negligible.mul_pow`/`Negligible.const_mul` with `C(q n + 1, 2) ≤ (q n + 1)^2 ≤ C'(n + 1)^{2d}`
from `PolyExpr.eval_le` (`Nat.choose_le_pow`); `Negligible.add` twice, and by maximality
`ε n := ` this sum bounds the advantage for every `n, m, m'`. -/
theorem prfScheme_multiMessageSecure (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (hF : PRF F) (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)) :
    (prfScheme F E hE hFE).MultiMessageSecure := by
  refine (PrivateKeyScheme.multiMessageSecure_iff _).2 fun D q => ?_
  -- the worst message pair at each parameter (hard-wired into the reductions)
  have hmax : ∀ n, ∃ p : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool),
      ∀ w : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool),
        distAdv ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.1)
            ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.2) (D.distinguisherL n) ≤
          distAdv ((prfScheme F E hE hFE).multiEncDist n (q.eval n) p.1)
            ((prfScheme F E hE hFE).multiEncDist n (q.eval n) p.2) (D.distinguisherL n) := by
    intro n
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
      (fun w : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool) =>
        distAdv ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.1)
          ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.2) (D.distinguisherL n))
      Finset.univ_nonempty
    exact ⟨p, fun w => hp w (Finset.mem_univ w)⟩
  choose μ hμ using hmax
  -- the next-query machines of Thm-99.2.1 for the two hard-wired message vectors
  obtain ⟨B₀, hB₀⟩ := MultiMsg.exists_queryChain_nuppt D q fun n => (μ n).1
  obtain ⟨B₁, hB₁⟩ := MultiMsg.exists_queryChain_nuppt D q fun n => (μ n).2
  refine ⟨fun n => prfAdv (F n) (B₀.toOracleAdversary n n n (q.eval n + 1)) +
      prfAdv (F n) (B₁.toOracleAdversary n n n (q.eval n + 1)) +
      2 * ((Nat.choose (q.eval n + 1) 2 : ℝ) / 2 ^ n), ?_, fun n m m' => ?_⟩
  · -- the asymptotic step: two PRF advantages and the collision term
    simpa only [PolyExpr.eval_add, PolyExpr.eval_const] using
      ((hF.negligible_prfAdv B₀ (.add q (.const 1))).add
        (hF.negligible_prfAdv B₁ (.add q (.const 1)))).add
        ((MultiMsg.negligible_choose_div_two_pow q).const_mul 2)
  · refine (hμ n (m, m')).trans ?_
    -- the concrete step: the ciphertext tuples are `encodeTuple ∘ prfEncReal`
    have key : ∀ m₀ : Fin (q.eval n + 1) → Fin n → Bool,
        (prfScheme F E hE hFE).multiEncDist n (q.eval n) m₀ =
          fun r => encodeTuple (prfEncReal (F n) m₀ (prfScheme_coinsEquiv F E hE hFE n (q.eval n) r)) :=
      fun m₀ => funext fun r => prfScheme_multiEncDist F E hE hFE n (q.eval n) m₀ r
    -- the machine step: the oracle adversaries of `B₀`, `B₁` are the `multiMsgAdv`
    have hadv : ∀ (B : NUPPT) (v : Fin (q.eval n + 1) → Fin n → Bool)
        (φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n),
        (∀ (g : (Fin n → Bool) → (Fin n → Bool)) ρ c,
          (B.toOracleAdversary n n n (q.eval n + 1) (φ (ρ, c))).eval g =
            decide (D.runAt n (List.ofFn fun j =>
              pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v j + g (ρ j)))) []).flatten c =
                [true])) →
        prfAdv (F n) (B.toOracleAdversary n n n (q.eval n + 1)) =
          prfAdv (F n) (multiMsgAdv v fun w c => D.distinguisherL n (encodeTuple w) c) := by
      intro B v φ hφ
      refine MultiMsg.prfAdv_congr_equiv (F n) _ _ φ fun g w => ?_
      rw [hφ g w.1 w.2, eval_multiMsgAdv, NUPPT.distinguisherL_eq, encodeTuple_eq_flatten]
    obtain ⟨φ₀, hφ₀⟩ := hB₀ n
    obtain ⟨φ₁, hφ₁⟩ := hB₁ n
    dsimp only
    rw [hadv B₀ (μ n).1 φ₀ hφ₀, hadv B₁ (μ n).2 φ₁ hφ₁, key, key, distAdv_def,
      acceptProb_comp_equiv (prfScheme_coinsEquiv F E hE hFE n (q.eval n))
        (fun s => encodeTuple (prfEncReal (F n) (μ n).1 s)),
      acceptProb_comp_equiv (prfScheme_coinsEquiv F E hE hFE n (q.eval n))
        (fun s => encodeTuple (prfEncReal (F n) (μ n).2 s)), ← distAdv_def]
    exact (distAdv_comp encodeTuple (prfEncReal (F n) (μ n).1) (prfEncReal (F n) (μ n).2)
      (D.distinguisherL n)).symm.trans_le (distAdv_prfEncReal_le (F n) (μ n).1 (μ n).2
        (fun w c => D.distinguisherL n (encodeTuple w) c))

/-- **Multi-message secure private-key encryption exists if a PRF exists** ([PS10, §3.9]):
the scheme of Algorithm 99.1 with the evaluator of `PRF.easy`. -/
theorem exists_multiMessageSecure_of_prf {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)}
    (hF : PRF F) : ∃ S : PrivateKeyScheme, S.MultiMessageSecure :=
  let ⟨E, hE, hFE⟩ := hF.easy
  ⟨prfScheme F E hE hFE, prfScheme_multiMessageSecure F hF E hE hFE⟩

/-- **Multi-message secure private-key encryption exists if a PRG exists** ([PS10, Theorems
97.3 and 99.2] combined): GGM gives a PRF, Algorithm 99.1 gives the scheme. -/
theorem exists_multiMessageSecure_of_exists_prg (h : ∃ P : PRG, P.Secure) :
    ∃ S : PrivateKeyScheme, S.MultiMessageSecure :=
  let ⟨_, hF⟩ := exists_prf_of_exists_prg h
  exists_multiMessageSecure_of_prf hF

end TCSlib.Cryptography
