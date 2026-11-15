/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionMulti.SliceParser
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionMulti.SliceReduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Joint, length-generic multi-message security of special encryption

[PS10, Algorithm 157.2] encrypts `m` as `⟨r, (0^n ‖ m) ⊕ f_k(r)⟩`. Yao's protocol uses it in two
layers with two pseudorandom families `G₁` (`2n`-bit outputs, `n`-bit messages) and `G₂`
(`n + (4n + 2)`-bit outputs, `(4n + 2)`-bit messages), and one wire key may key both
(`GarblingSpecial.lean`, `Yao.lean`). The hybrid of `yaoHybrid_simulators` (step 3) needs
multi-message security of both layers *under one key*. Under the joint hypothesis `hG₁₂`, both
layers read their pads from one family `G = G₁ ‖ G₂`, at different offsets.

This module states that property for any `PRFOut` family `G` with `ℓ(n)`-bit outputs. A
ciphertext is cut from a **slice** of `G_k(r)`: the pad of the `i`-th ciphertext is
`G_k(r_i)_{[o_i, o_i + n + ℓ_i)}` for an offset `o_i` and a message length `ℓ_i`, both chosen
per ciphertext. Polynomially many slice ciphertexts under one key `k ← U_n`, with independent
nonces `r_i ← U_n`, are indistinguishable for any two message vectors, uniformly in the slices.
The frozen `specialScheme_multiMessageSecure` (one family, `n`-bit messages) is the corollary
with every slice `(0, n)` (`specialScheme_multiMessageSecure_of_joint`, proved here).

**Placement.** A new module beside `SpecialEncryptionSecurity.lean`, not inside it: this
statement PR is additive and leaves that file (frozen statements, owned by the garbling unit)
byte-identical. It imports `SpecialEncryptionSecurity` for `PRFOut` and `specialScheme`;
`yaoHybrid_simulators`' helper modules import it.

**B3.** The statement uses only existing definitions (`PRFOut`, `spEncStr`, the private-key
`encodeList`, `distAdv`, `NUPPT.distinguisherL`). Its proof needs the PRF hybrid machinery with
`ℓ`-bit outputs, which the separate job `prf-long` provides (ruling B3, 2026-11-14).

## Main definitions

* `SecureComputation.sliceEnc`: Algorithm 157.2 with the pad `G_k(r)_{≥o}` (a slice of `G_k(r)`).
* `SecureComputation.sliceMultiEncDist`: `q + 1` slice ciphertexts under one key.
* `SecureComputation.SliceMultiMessageSecure`: their indistinguishability for any two message
  vectors, uniformly in the slices.

## Main results

* `SecureComputation.sliceMultiMessageSecure_of_prfOut` (proved): every `PRFOut` family is
  slice multi-message secure (ruling B1, 2026-11-14).
* `SecureComputation.specialScheme_multiMessageSecure_of_joint` (proved): the frozen Claim
  157.a (i) follows.
* `SecureComputation.sliceEnc_eq_spEncStr`, `sliceEnc_append_left`, `sliceEnc_append_right`
  (proved): slice ciphertexts are special ciphertexts, in particular those of the two layers of
  `nestedSpecial` under `G₁ ‖ G₂`.

## Contents

* `SpecialEncryptionMulti.SliceParser`: the total efficient slice post-processor.
* `SpecialEncryptionMulti.SliceReduction`: polynomial advice, the reduction machine and
  the same-seed D4 tuple identity.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.7 (Definition 93.1, Theorem 99.2) and §6.2.2 (Algorithm 157.2, book pp. 156–157).
* [LP09] Y. Lindell, B. Pinkas, *A proof of security of Yao's protocol for two-party computation*,
  Journal of Cryptology 22(2), 2009, pp. 161–188 (the hybrid with one inactive key per step).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

/-! ### Slice ciphertexts -/

/-- **A slice ciphertext**: Algorithm 157.2 [PS10, §6.2.2] under the key `k` with nonce `r`, whose
pad is the slice `p = G_k(r)_{≥o}` of the family's output from offset `o`. That is `spEncStr`
with the constant evaluator `p`, the ciphertext `⟨r, p_{<n} ‖ (m ⊕ p_{≥n})⟩`, where `m` uses
the pad bits `G_k(r)_{[o + n, o + n + |m|)}`. -/
def sliceEnc {L : ℕ → ℕ} (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool))
    (n o : ℕ) (k r : Fin n → Bool) (m : List Bool) : List Bool :=
  spEncStr (fun _ => (List.ofFn (G n k r)).drop o) (List.ofFn k) m (List.ofFn r)

/-- A slice ciphertext is `spEncStr` with the constant pad `G_k(r)_{≥o}`:
`sliceEnc G n o k r m = spEncStr (fun _ => ⟦G_k(r)⟧.drop o) ⟦k⟧ m ⟦r⟧`. -/
theorem sliceEnc_eq {L : ℕ → ℕ} (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool))
    (n o : ℕ) (k r : Fin n → Bool) (m : List Bool) :
    sliceEnc G n o k r m =
      spEncStr (fun _ => (List.ofFn (G n k r)).drop o) (List.ofFn k) m (List.ofFn r) := rfl

/-- **Slices of an evaluated family**: if `E` evaluates `G` (`E(⟨s, x⟩) = G_s(x)`), the slice
ciphertext from offset `o` is the special ciphertext with the evaluator `z ↦ E(z)_{≥o}`:
`sliceEnc G n o k r m = spEncStr (fun z => (E z).drop o) ⟦k⟧ m ⟦r⟧`. -/
theorem sliceEnc_eq_spEncStr {L : ℕ → ℕ}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)} {E : List Bool → List Bool}
    (hGE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G n s x))
    (n o : ℕ) (k r : Fin n → Bool) (m : List Bool) :
    sliceEnc G n o k r m = spEncStr (fun z => (E z).drop o) (List.ofFn k) m (List.ofFn r) := by
  rw [sliceEnc_eq, spEncStr_eq, spEncStr_eq, hGE]

/-- Masking with a longer pad uses only its first `|m|` bits. -/
private theorem zipWith_xor_append_of_le : ∀ (m p b : List Bool), m.length ≤ p.length →
    List.zipWith xor m (p ++ b) = List.zipWith xor m p
  | [], _, _, _ => by simp
  | _ :: _, [], _, h => by simp at h
  | a :: m, c :: p, b, h => by
    simp only [List.cons_append, List.zipWith_cons_cons, List.cons.injEq, true_and]
    exact zipWith_xor_append_of_le m p b (by simpa using h)

/-- **The inner layer as a slice of `G₁ ‖ G₂`**: if `⟦G_k(r)⟧ = ⟦G₁_k(r)⟧ ++ ⟦G₂_k(r)⟧` and `E₁`
evaluates `G₁` (`2n`-bit outputs), then for `|m| ≤ n` the slice from offset `0` is the
`G₁`-ciphertext: `sliceEnc G n 0 k r m = spEncStr E₁ ⟦k⟧ m ⟦r⟧`. -/
theorem sliceEnc_append_left {L L₂ : ℕ → ℕ}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)}
    {G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool)}
    {G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L₂ n) → Bool)} {E₁ : List Bool → List Bool}
    (hG : ∀ n (s x : Fin n → Bool),
      List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x))
    (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G₁ n s x))
    (n : ℕ) (k r : Fin n → Bool) {m : List Bool} (hm : m.length ≤ n) :
    sliceEnc G n 0 k r m = spEncStr E₁ (List.ofFn k) m (List.ofFn r) := by
  have h₁ : (List.ofFn (G₁ n k r)).length = n + n := List.length_ofFn
  rw [sliceEnc_eq, spEncStr_eq, spEncStr_eq, hGE₁, List.drop_zero, hG, List.length_ofFn,
    List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
    zipWith_xor_append_of_le _ _ _ (by rw [List.length_drop]; omega)]

/-- **The outer layer as a slice of `G₁ ‖ G₂`**: if `⟦G_k(r)⟧ = ⟦G₁_k(r)⟧ ++ ⟦G₂_k(r)⟧` with `G₁`
of `2n`-bit outputs and `E₂` evaluates `G₂`, the slice from offset `2n` is the `G₂`-ciphertext:
`sliceEnc G n (n + n) k r m = spEncStr E₂ ⟦k⟧ m ⟦r⟧`, for every message `m`. -/
theorem sliceEnc_append_right {L L₂ : ℕ → ℕ}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)}
    {G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool)}
    {G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L₂ n) → Bool)} {E₂ : List Bool → List Bool}
    (hG : ∀ n (s x : Fin n → Bool),
      List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x))
    (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G₂ n s x))
    (n : ℕ) (k r : Fin n → Bool) (m : List Bool) :
    sliceEnc G n (n + n) k r m = spEncStr E₂ (List.ofFn k) m (List.ofFn r) := by
  rw [sliceEnc_eq, spEncStr_eq, spEncStr_eq, hGE₂, hG, List.drop_left' List.length_ofFn]

/-! ### Joint multi-message security -/

/-- **`q + 1` slice ciphertexts under one key** (the sampler of [PS10, Definition 93.1], with
slices): from the key `k` and the nonces `r_0, …, r_q` (the seed `(k, r)`, uniform), the
`encodeList` of `sliceEnc G n o_i k r_i m_i` for `i ≤ q`, i.e. of
`⟨r_i, (0^n ‖ m_i) ⊕ G_k(r_i)_{[o_i, o_i + n + ℓ_i)}⟩` with `m_i ∈ {0,1}^{ℓ_i}`. -/
def sliceMultiEncDist {L : ℕ → ℕ}
    (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)) (n q : ℕ)
    (o len : Fin (q + 1) → ℕ) (m : ∀ i, Fin (len i) → Bool) :
    (Fin n → Bool) × (Fin (q + 1) → Fin n → Bool) → List Bool :=
  fun t => PrivateKeyScheme.encodeList
    (List.ofFn fun i => sliceEnc G n (o i) t.1 (t.2 i) (List.ofFn (m i)))

/-- The slice sampler at the seed `t = (k, r)` is the `encodeList` of the `q + 1` ciphertexts
`sliceEnc G n o_i k r_i ⟦m_i⟧`. -/
theorem sliceMultiEncDist_apply {L : ℕ → ℕ}
    (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)) (n q : ℕ)
    (o len : Fin (q + 1) → ℕ) (m : ∀ i, Fin (len i) → Bool)
    (t : (Fin n → Bool) × (Fin (q + 1) → Fin n → Bool)) :
    sliceMultiEncDist G n q o len m t = PrivateKeyScheme.encodeList
      (List.ofFn fun i => sliceEnc G n (o i) t.1 (t.2 i) (List.ofFn (m i))) := rfl

/-- **Slice multi-message security** of a family `G` with `L(n)`-bit outputs ([PS10,
Definition 93.1], with slices and one key): for every non-uniform PPT `D` and polynomial `q`
there is a negligible `ε` such that for all `n`, all offsets and lengths `o, ℓ ∈ ℕ^{q(n)+1}`
with `o_i + n + ℓ_i ≤ L(n)`, and all `m, m'` with `m_i, m'_i ∈ {0,1}^{ℓ_i}`,
`|Pr[k, r ← U : D(1^n, ⟨Enc^{o_i}_k(m_i; r_i)⟩_i) = 1] − Pr[… m' …]| ≤ ε(n)`, where
`Enc^o_k(m; r) = sliceEnc G n o k r m`.

`ε` precedes the slices as well as the messages, so a reduction may choose the slices by advice.
With every slice `(0, n)` and `L(n) = 2n` this is `PrivateKeyScheme.MultiMessageSecure` of
`specialScheme` (`specialScheme_multiMessageSecure_of_joint`).

**Deviation:** `D` receives `1^n`; the ciphertexts are encoded by `encodeList` (as in
`MultiMessageSecure`). -/
def SliceMultiMessageSecure {L : ℕ → ℕ}
    (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)) : Prop :=
  ∀ (D : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (o len : Fin (q.eval n + 1) → ℕ), (∀ i, o i + n + len i ≤ L n) →
      ∀ m m' : ∀ i, Fin (len i) → Bool,
        distAdv (sliceMultiEncDist G n (q.eval n) o len m)
          (sliceMultiEncDist G n (q.eval n) o len m') (D.distinguisherL n) ≤ ε n

/-- The defining property of `SliceMultiMessageSecure`: for every `D` and `q` a negligible `ε`
bounds `D`'s advantage between the slice ciphertexts of any two message vectors, for every
slice vector that fits in `L(n)`. -/
theorem sliceMultiMessageSecure_iff {L : ℕ → ℕ}
    (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool)) :
    SliceMultiMessageSecure G ↔ ∀ (D : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (o len : Fin (q.eval n + 1) → ℕ), (∀ i, o i + n + len i ≤ L n) →
        ∀ m m' : ∀ i, Fin (len i) → Bool,
          distAdv (sliceMultiEncDist G n (q.eval n) o len m)
            (sliceMultiEncDist G n (q.eval n) o len m') (D.distinguisherL n) ≤ ε n := Iff.rfl

/-- **Joint, length-generic multi-message security** (ruling B1, 2026-11-14) [PS10, §6.2.2, "it
is easy to modify construction 99.1"; Definition 93.1, Theorem 99.2]: every pseudorandom family
`G` with `ℓ(n)`-bit outputs (`PRFOut ℓ G`) is slice multi-message secure. For every
non-uniform PPT `D` and polynomial `q` there is a negligible `ε` with, for all `n`, all slices
`(o_i, ℓ_i)_{i ≤ q(n)}` with `o_i + n + ℓ_i ≤ ℓ(n)` and all `m, m'` with `|m_i| = |m'_i| = ℓ_i`,
`|Pr[D(1^n, ⟨r_i, (0^n ‖ m_i) ⊕ G_k(r_i)_{[o_i, o_i+n+ℓ_i)}⟩_i) = 1] − Pr[… m' …]| ≤ ε(n)`
over `k, r_0, …, r_{q(n)} ← U_n`.

**Corollaries.**
- `specialScheme_multiMessageSecure` (frozen Claim 157.a (i)) is
  `specialScheme_multiMessageSecure_of_joint G E hE hGE (sliceMultiMessageSecure_of_prfOut hG)`:
  every slice is `(0, n)` and `ℓ(n) = 2n`.
- Step 3 of `yaoHybrid_simulators` takes `G = G₁ ‖ G₂` under `hG₁₂`, with
  `ℓ(n) = 2n + (n + (4n + 2))`. The rows under the inactive key `ι_u` where `u` is a second or
  only argument are slices `(0, n)` (`sliceEnc_append_left`: the `G₁`-ciphertexts
  `spEncStr E₁`). Those where `u` is a first argument are slices `(2n, 4n + 2)`
  (`sliceEnc_append_right`: the `G₂`-ciphertexts `spEncStr E₂`). Both shapes fit; the outer
  slice fits exactly. The bound is uniform in the slices, so the reduction's advice may fix
  which rows, of which layer, it embeds.

**Deviations.** [PS10] states the claim for one scheme and `n`-bit messages. Here the claim is
length-generic and joint: the pads of different ciphertexts may come from different slices
of one family under one key. The fit `o_i + n + ℓ_i ≤ ℓ(n)` keeps every pad inside `G_k(r_i)`.

**Proof sketch.** Fix `D,q`. A configuration records fitting offsets and lengths bounded
by `ℓ(n)`, together with two finite message vectors. Maximize the slice advantage over
`Option` of these configurations, assigning `none` the value zero. This gives maximum zero
when no slices fit. Encode the maximizing slice vector as polynomial-length unary advice.
The total polynomial-time post-map parses descriptors and ciphertexts in parallel, keeping
each nonce and taking `(body.drop o_i).take (n+len_i)`.

For a fitting vector, use the full-width masks
`0^{o_i+n} ++ m_i ++ 0^{ℓ(n)-(o_i+n+len_i)}`. The post-map of D4's encoded real tuple is
pointwise the slice sampler on exactly the same key/nonce seed (`slicePost_tuple` and the
shared `spEncStr_eq_sliceMask`). Precompose `D` with the parser and hard-wire its advice using
the published NUPPT closure theorems. D4 supplies one negligible bound before these masks.
The coin equivalence and `distAdv_comp` transfer it to the maximizing pair, which bounds all
fitting choices. If the maximizing choice is `none`, D4 on equal zero masks supplies the
required nonnegative error bound. The PRF step, uniform random pads, collision term and
triangle bound all remain inside D4 and are not reconstructed here. -/
theorem sliceMultiMessageSecure_of_prfOut {ℓ : PolyExpr}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)} (hG : PRFOut ℓ G) :
    SliceMultiMessageSecure G := by
  classical
  rw [sliceMultiMessageSecure_iff]
  intro D q
  -- A finite configuration stores bounded offsets and lengths, and its fit proof.
  let Config : ℕ → Type := fun n =>
    {c : (Fin (q.eval n + 1) → Fin (ℓ.eval n + 1)) ×
      (Fin (q.eval n + 1) → Fin (ℓ.eval n + 1)) //
        ∀ i, (c.1 i).val + n + (c.2 i).val ≤ ℓ.eval n}
  let off (n : ℕ) (c : Config n) : Fin (q.eval n + 1) → ℕ := fun i => (c.1.1 i).val
  let len (n : ℕ) (c : Config n) : Fin (q.eval n + 1) → ℕ := fun i => (c.1.2 i).val
  let Msg (n : ℕ) (c : Config n) := (i : Fin (q.eval n + 1)) → Fin (len n c i) → Bool
  let Pack (n : ℕ) := (c : Config n) × (Msg n c × Msg n c)
  let adv (n : ℕ) (p : Option (Pack n)) : ℝ := p.elim 0 fun p =>
    distAdv (sliceMultiEncDist G n (q.eval n) (off n p.1) (len n p.1) p.2.1)
      (sliceMultiEncDist G n (q.eval n) (off n p.1) (len n p.1) p.2.2) (D.distinguisherL n)
  -- Adding `none` with value zero implements the empty-fit-set convention.
  have hmax : ∀ n, ∃ p : Option (Pack n), ∀ w, adv n w ≤ adv n p := by
    intro n
    obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image Finset.univ (adv n) Finset.univ_nonempty
    exact ⟨p, fun w => hmax w (Finset.mem_univ _)⟩
  choose μ hμ using hmax
  let β : ℕ → List Bool := fun n => (μ n).elim [] fun p =>
    SliceReduction.sliceAdvice n (off n p.1) (len n p.1)
  let b : PolyExpr := .mul (.add q (.const 1)) (.add (.mul (.const 6) ℓ) (.const 6))
  have hβlen : ∀ n, (β n).length ≤ b.eval n := by
    intro n
    cases hc : μ n with
    | none => simp only [β, hc, Option.elim_none, List.length_nil, Nat.zero_le]
    | some p =>
      have h := SliceReduction.length_sliceAdvice_le (ℓ.eval n) n
        (off n p.1) (len n p.1) p.1.2
      simpa only [β, hc, Option.elim_some, b, PolyExpr.eval_mul, PolyExpr.eval_add,
        PolyExpr.eval_const] using h
  obtain ⟨B, hB⟩ := SliceReduction.exists_slicePost_nuppt D β b hβlen
  obtain ⟨ε, hε, hb⟩ := MultiMsg.exists_negligible_distAdv_prfEncRealOut hG.pseudorandom B q
  refine ⟨ε, hε, fun n o l hfit m m' => ?_⟩
  let c : Config n := ⟨((fun i => ⟨o i, by have h := hfit i; omega⟩),
    (fun i => ⟨l i, by have h := hfit i; omega⟩)), hfit⟩
  have hdom := hμ n (some ⟨c, m, m'⟩)
  change distAdv _ _ _ ≤ ε n
  refine hdom.trans ?_
  cases hc : μ n with
  | none =>
    have hz := hb n (fun _ _ => false) (fun _ _ => false)
    rw [distAdv_def, sub_self, abs_zero] at hz
    simpa only [adv, hc, Option.elim_none] using hz
  | some p =>
    obtain ⟨e, he⟩ := hB n
    let P : List Bool → List Bool := fun z => SliceReduction.slicePost (pairEncode (β n) z)
    let W : Msg n p.1 → Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool := fun v i =>
      sliceMask (ℓ.eval n) n (off n p.1 i) (List.ofFn (v i))
    let X (v : Msg n p.1) := fun t => encodeTupleOut (prfEncRealOut (G n) (W v) t)
    have hadvice : β n = SliceReduction.sliceAdvice n (off n p.1) (len n p.1) := by
      simp only [β, hc, Option.elim_some]
    have hsampler (v : Msg n p.1) :
        sliceMultiEncDist G n (q.eval n) (off n p.1) (len n p.1) v =
          fun t => P (X v t) := by
      funext t
      rw [sliceMultiEncDist_apply]
      dsimp only [P, X, W]
      rw [hadvice, SliceReduction.slicePost_tuple (G n) _ _ p.1.2]
      apply congrArg PrivateKeyScheme.encodeList
      apply congrArg List.ofFn
      funext i
      rw [sliceEnc_eq]
    have hcoin : ∀ z r, B.distinguisherL n z (e r) = D.distinguisherL n (P z) r := he
    have hadv : distAdv (X p.2.1) (X p.2.2)
        (fun z r => D.distinguisherL n (P z) r) =
          distAdv (X p.2.1) (X p.2.2) (B.distinguisherL n) := by
      symm
      rw [distAdv_def, distAdv_def,
        acceptProb_coins_equiv (X p.2.1) (B.distinguisherL n) _ e hcoin,
        acceptProb_coins_equiv (X p.2.2) (B.distinguisherL n) _ e hcoin]
    change distAdv (sliceMultiEncDist G n (q.eval n) (off n p.1) (len n p.1) p.2.1)
      (sliceMultiEncDist G n (q.eval n) (off n p.1) (len n p.1) p.2.2)
        (D.distinguisherL n) ≤ ε n
    rw [hsampler p.2.1, hsampler p.2.2, ← distAdv_comp P, hadv]
    exact hb n (W p.2.1) (W p.2.2)

/-! ### The frozen Claim 157.a (i) as a corollary -/

section Corollary

variable (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hGE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G n s x))

/-- **The frozen Claim 157.a (i) from the joint lemma** [PS10, §6.2.2, Definition 93.1]: if the
length-doubling family `G` is slice multi-message secure, then `specialScheme G E hE hGE` is
multi-message secure. With `sliceMultiMessageSecure_of_prfOut` this gives
`specialScheme_multiMessageSecure`.

**Proof sketch.** Take every slice to be `(0, n)`; it fits, as `0 + n + n ≤ 2n`. Relabel the
coins of `Gen` and `Enc` as an `n`-bit key and `n`-bit nonces, keeping their strings. Under this
bijection the scheme's multi-message sampler is the slice sampler pointwise: `Gen` outputs its
coins (`runAt_coinKey`), `Enc` is `spEncStr E` (`runAt_spEnc`), and a slice from offset `0` is
`spEncStr E` (`sliceEnc_eq_spEncStr`). Acceptance probabilities are invariant under relabelling
the seed (`acceptProb_comp_equiv`), so the slice bound applies verbatim. -/
theorem specialScheme_multiMessageSecure_of_joint (h : SliceMultiMessageSecure G) :
    (specialScheme G E hE hGE).MultiMessageSecure := by
  rw [PrivateKeyScheme.multiMessageSecure_iff]
  intro D q
  obtain ⟨ε, hε, hb⟩ := (sliceMultiMessageSecure_iff G).mp h D q
  refine ⟨ε, hε, fun n m m' => ?_⟩
  let e : (specialScheme G E hE hGE).gen.Coins n ×
      (Fin (q.eval n + 1) → (specialScheme G E hE hGE).enc.Coins n) ≃
      (Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool) :=
    (specialScheme_keyCoinsEquiv G E hE hGE n).prodCongr
      (Equiv.piCongrRight fun _ => specialScheme_nonceCoinsEquiv G E hE hGE n)
  have hX : ∀ v : Fin (q.eval n + 1) → Fin n → Bool,
      (specialScheme G E hE hGE).multiEncDist n (q.eval n) v =
        fun t => sliceMultiEncDist G n (q.eval n) (fun _ => 0) (fun _ => n) v (e t) := by
    intro v
    funext t
    rw [PrivateKeyScheme.multiEncDist_apply, sliceMultiEncDist_apply]
    refine congrArg PrivateKeyScheme.encodeList (congrArg List.ofFn (funext fun i => ?_))
    rw [specialScheme_gen_runAt, specialScheme_enc_runAt, sliceEnc_eq_spEncStr hGE]
    simp only [e, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.piCongrRight_apply,
      Pi.map_apply, List.drop_zero, specialScheme_keyCoinsEquiv_ofFn,
      specialScheme_nonceCoinsEquiv_ofFn]
  rw [distAdv_def, hX m, hX m', acceptProb_comp_equiv, acceptProb_comp_equiv, ← distAdv_def]
  exact hb n (fun _ => 0) (fun _ => n) (fun _ => by show 0 + n + n ≤ n + n; omega) m m'

end Corollary

end TCSlib.Cryptography.SecureComputation
