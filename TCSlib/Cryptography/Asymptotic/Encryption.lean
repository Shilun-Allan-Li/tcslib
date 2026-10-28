/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Pseudorandom

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Private-key encryption: single- and multi-message security

The computational definitions of secure private-key encryption of [PS10, §2.1.3, §3.5–§3.7]
on top of the machine layer `Complexity.NUPPT` (foundation decisions D3–D6 of
`PassShelatChapter2-4Plan.md`): an *efficient private-key encryption scheme* is a triple of
PPTs `(Gen, Enc, Dec)` with perfect correctness [PS10, Definition 24.7]; it is
*single-message secure* when the encryptions of any two messages are computationally
indistinguishable [PS10, Definition 91.1] and *multi-message secure* when the encryptions of
any two vectors of polynomially many messages under one key are [PS10, Definition 93.1].
The section's construction is the one-time pad with a pseudorandom pad
[PS10, Algorithm 92.1], secure by the four-hybrid argument [PS10, Theorem 92.2], and the
section's impossibility result is that a deterministic (stateless) scheme is never
multi-message secure [PS10, Theorem 94.2].

The file has the two layers of D2.

* **Concrete** (one `n`, samplers and adversaries as functions of uniform coins): the
  truncated one-time pad `padXor` (an `n`-bit message masked by the first `n` bits of an
  `L`-bit pad), its perfect secrecy `acceptProb_padXor` (Claim-92.a: `m ⊕ U` is uniform, so
  `m₀ ⊕ U` and `m₁ ⊕ U` are identically distributed), and the exact four-hybrid bound
  `distAdv_padXor_le`: a distinguisher of `m₀ ⊕ G(U_n)` from `m₁ ⊕ G(U_n)` has advantage at
  most the sum of two PRG advantages `prgAdv G (D ∘ (mᵢ ⊕ ·))` [PS10, Theorem 92.2, proof].
* **Asymptotic**: `PrivateKeyScheme`, `SingleMessageSecure`, `MultiMessageSecure`, the
  scheme `prgScheme` of Algorithm 92.1 as a `PrivateKeyScheme` value built from
  `Complexity.NUPPT.ofPolyTimeUniform` of the FP functions `pairSndD` (the key is the coin
  string) and `prgPadFun` (`Complexity.polyTimeComputable_pairXor`), its correctness proved,
  its security `prgScheme_singleMessageSecure` proved by the four-hybrid argument (the
  message pair hard-wired as advice, `Complexity.NUPPT.exists_withAdvice`), and
  Theorem 94.2 proved (`not_multiMessageSecure_of_deterministic`) with the text's two-message
  distinguisher `[c₀ = c₁]` (`Complexity.polyTimeComputable_pairEq`).

**Deviation:** `PrivateKeyScheme`: messages at parameter `n` are the `n`-bit strings
(the text's `m ∈ {0,1}^n`), keys and ciphertexts arbitrary strings; `Enc` and `Dec` are
activated at parameter `n` on `⟨1^n, ⟨k, ·⟩⟩` (time polynomial in `n`; the text's "polynomial
in the size of their inputs" agrees since `|k| ≤ poly(n)`); correctness holds for every coin
string of `Gen`, `Enc` and `Dec` (the probability-one reading of [PS10, Definition 24.6],
`Complexity.NUPPT.computes_iff_uprob`); `Dec`'s `⊥` is any output that does not decode to an
`n`-bit string (`decodeFin`).

**Deviation:** `SingleMessageSecure`, `MultiMessageSecure`: the distinguisher receives `1^n`
with the ciphertext(s) (D5); the bound is `≤ ε(n)` (the text's "at most"); the `q(n) + 1`
ciphertexts of Definition 93.1 are encoded as a nested pair `encodeList`.

**Deviation:** `prgScheme` (Algorithm 92.1): the key is an `n`-bit seed and the pad is the
first `n` bits of `G(k)` (the text's `n/2`-bit key for a length-doubling `G` requires `n`
even; with syntactic polynomial lengths (D9) a key length that is a non-constant function of
the message length is never shorter than the message, so the "short key" economy of §3.6 is a
matter of parametrization and the security argument, the four hybrids, is unchanged); the
evaluator `F` of `G` is an explicit argument rather than extracted from `PRG.Easy`.

**Deviation:** `not_multiMessageSecure_of_deterministic` (Theorem 94.2): "stateless" is built
into the model (an `NUPPT` has no state between activations); "deterministic" is
`PrivateKeyScheme.Deterministic` (the output of `Enc` does not depend on its coins); the
proof uses correctness (to get `c'₀ ≠ c'₁`) and `n ≥ 1` (two distinct messages), both
implicit in the text.

## Main definitions

* `TCSlib.Cryptography.PrivateKeyScheme` — an efficient private-key encryption scheme
  [PS10, Definition 24.7]; `PrivateKeyScheme.encDist` — `{k ← Gen(1^n) : Enc_k(m)}`;
  `PrivateKeyScheme.multiEncDist`, `PrivateKeyScheme.encodeList` — the vector of
  `q + 1` encryptions under one key.
* `TCSlib.Cryptography.PrivateKeyScheme.SingleMessageSecure` — [PS10, Definition 91.1].
* `TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure` — [PS10, Definition 93.1].
* `TCSlib.Cryptography.PrivateKeyScheme.Deterministic` — `Enc` ignores its coins.
* `TCSlib.Cryptography.padXor` — the truncated one-time pad `m ⊕ p|_n`.
* `TCSlib.Cryptography.prgPadFun`, `TCSlib.Cryptography.prgScheme` — the scheme of
  [PS10, Algorithm 92.1].

## Main results

* `TCSlib.Cryptography.acceptProb_padXor` — perfect secrecy of the one-time pad (Claim-92.a).
* `TCSlib.Cryptography.distAdv_padXor_le` — the concrete four-hybrid bound of
  [PS10, Theorem 92.2].
* `TCSlib.Cryptography.prgScheme_encDist` — the ciphertext distribution of Algorithm 92.1 is
  `m ⊕ G(U_n)|_n`.
* `TCSlib.Cryptography.prgScheme_singleMessageSecure` — [PS10, Theorem 92.2].
* `TCSlib.Cryptography.PrivateKeyScheme.not_multiMessageSecure_of_deterministic` —
  [PS10, Theorem 94.2].
* `TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure.singleMessageSecure` —
  multi-message security implies single-message security (the sanity direction of
  [PS10, §3.7, "extends"]).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1.3: Definition 24.7; §3.5: Definition 91.1; §3.6: Algorithm 92.1, Theorem 92.2;
  §3.7: Definition 93.1, Theorem 94.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.2–3.3 (the concrete `distAdv`, `prgAdv`, Lemma 3.2).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Transporting a distinguisher along an equality of coin polynomials -/

/-- **Transport of a distinguisher along `A.coins = B.coins`**: if the activations of `A` on
`X s` and of `B` on `Y s` agree for every seed `s` and every coin string, then the acceptance
probabilities of `A` on `X` and of `B` on `Y` agree. The coin types `A.Coins n` and
`B.Coins n` are identified by `finCongr` (`List.ofFn_congr`) and the seed spaces relabelled
by `uprob_comp_equiv`. This is the bridge by which a machine obtained from the closure
calculus (`Complexity.NUPPT.exists_comp`, `NUPPT.exists_withAdvice`) is compared with the
given adversary. -/
private theorem acceptProb_distinguisherL_congr {σ : Type*} [Fintype σ] {A B : NUPPT}
    (hc : A.coins = B.coins) (n : ℕ) (X Y : σ → List Bool)
    (h : ∀ s r, A.runAtL n (X s) r = B.runAtL n (Y s) r) :
    acceptProb X (A.distinguisherL n) = acceptProb Y (B.distinguisherL n) := by
  have hlen : A.coinLen n = B.coinLen n := by simp only [NUPPT.coinLen, hc]
  let e : A.Coins n ≃ B.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  have hofn : ∀ r : A.Coins n, List.ofFn (e r) = List.ofFn r := fun r =>
    (List.ofFn_congr hlen r).symm
  unfold acceptProb
  have := uprob_comp_equiv ((Equiv.refl σ).prodCongr e)
    (fun z : σ × B.Coins n => B.distinguisherL n (Y z.1) z.2 = true)
  rw [← this]
  congr 1
  funext z
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply,
    NUPPT.distinguisherL, NUPPT.runAt_eq, h, hofn]

/-! ### Efficient private-key encryption [PS10, Definition 24.7] -/

/-- An **efficient private-key encryption scheme** [PS10, Definition 24.7]: three PPTs
(`Complexity.NUPPT`s with empty advice) — `Gen(1^n)` samples a key `k`, `Enc_k(m)` encrypts
an `n`-bit message, `Dec_k(c)` decrypts a ciphertext into an `n`-bit message or `⊥` — such
that for every `n`, every `m ∈ {0,1}^n` and every choice of coins,
`Dec_k(Enc_k(m)) = m` where `k ← Gen(1^n)` (clause (4), probability one).
`Enc` and `Dec` are activated at parameter `n` on the pair `⟨k, m⟩` resp. `⟨k, c⟩`; the
output of `Dec` is decoded as an `n`-bit string by `decodeFin` (`none` is `⊥`).

**Deviation:** `PrivateKeyScheme`: messages at parameter `n` are the `n`-bit strings, keys
and ciphertexts arbitrary strings; `Enc` and `Dec` are activated at parameter `n` on
`⟨1^n, ⟨k, ·⟩⟩`; correctness holds for every coin string (the probability-one reading of
[PS10, Definition 24.6], `Complexity.NUPPT.computes_iff_uprob`); `Dec`'s `⊥` is any output
that does not decode to an `n`-bit string. -/
structure PrivateKeyScheme where
  /-- The key generator `Gen(1^n)`. -/
  gen : NUPPT
  /-- The encryption algorithm `Enc_k(m)`, activated on `⟨k, m⟩`. -/
  enc : NUPPT
  /-- The decryption algorithm `Dec_k(c)`, activated on `⟨k, c⟩`. -/
  dec : NUPPT
  /-- `Gen` is a PPT (no advice). -/
  gen_uniform : gen.Uniform
  /-- `Enc` is a PPT (no advice). -/
  enc_uniform : enc.Uniform
  /-- `Dec` is a PPT (no advice). -/
  dec_uniform : dec.Uniform
  /-- Perfect correctness [PS10, Definition 24.7 (4)], for every coin string. -/
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n) (rd : dec.Coins n),
    decodeFin n (dec.runAt n (pairEncode (gen.runAt n [] rg)
      (enc.runAt n (pairEncode (gen.runAt n [] rg) (List.ofFn m)) re)) rd) = some m

namespace PrivateKeyScheme

/-- The ciphertext distribution `{k ← Gen(1^n) : Enc_k(m)}` of [PS10, Definition 91.1] as a
sampler from the coins of `Gen` and `Enc`. -/
def encDist (S : PrivateKeyScheme) (n : ℕ) (m : Fin n → Bool) :
    S.gen.Coins n × S.enc.Coins n → List Bool :=
  fun r => S.enc.runAt n (pairEncode (S.gen.runAt n [] r.1) (List.ofFn m)) r.2

/-- **Single-message security** [PS10, Definition 91.1]: for every non-uniform PPT `D` there
is a negligible `ε` such that for all `n` and all `m₀, m₁ ∈ {0,1}^n`, `D` distinguishes
`{k ← Gen(1^n) : Enc_k(m₀)}` from `{k ← Gen(1^n) : Enc_k(m₁)}` with advantage at most
`ε(n)`. The quantifier order (`ε` before `m₀, m₁`) is the text's.

**Deviation:** the distinguisher receives `1^n` with the ciphertext (D5); the bound is
`≤ ε(n)`. -/
def SingleMessageSecure (S : PrivateKeyScheme) : Prop :=
  ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (m₀ m₁ : Fin n → Bool),
    distAdv (S.encDist n m₀) (S.encDist n m₁) (D.distinguisherL n) ≤ ε n

/-- The encoding of a list of strings as a nested pair `⟨c₀, ⟨c₁, ⟨…, []⟩⟩⟩` (the tuple of
ciphertexts of [PS10, Definition 93.1]). -/
def encodeList : List (List Bool) → List Bool
  | [] => []
  | m :: ms => pairEncode m (encodeList ms)

/-- The distribution `{k ← Gen(1^n) : Enc_k(m₀), …, Enc_k(m_q)}` of [PS10, Definition 93.1]:
`q + 1` encryptions under one key with independent encryption coins, encoded by
`encodeList`. -/
def multiEncDist (S : PrivateKeyScheme) (n : ℕ) (q : ℕ) (m : Fin (q + 1) → Fin n → Bool) :
    S.gen.Coins n × (Fin (q + 1) → S.enc.Coins n) → List Bool :=
  fun r => encodeList (List.ofFn fun i =>
    S.enc.runAt n (pairEncode (S.gen.runAt n [] r.1) (List.ofFn (m i))) (r.2 i))

/-- **Multi-message security** [PS10, Definition 93.1]: for every non-uniform PPT `D` and
every polynomial `q` there is a negligible `ε` such that for all `n` and all message vectors
`m, m' ∈ ({0,1}^n)^{q(n)+1}`, `D` distinguishes the encryptions of `m` from those of `m'`
under one key `k ← Gen(1^n)` with advantage at most `ε(n)`. The count is `q(n) + 1`
messages (indices `0, …, q(n)`), as in the text.

**Deviation:** `D` receives `1^n`; the `q(n) + 1` ciphertexts are encoded by `encodeList`. -/
def MultiMessageSecure (S : PrivateKeyScheme) : Prop :=
  ∀ (D : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (m m' : Fin (q.eval n + 1) → Fin n → Bool),
      distAdv (S.multiEncDist n (q.eval n) m) (S.multiEncDist n (q.eval n) m') (D.distinguisherL n) ≤ ε n

/-- **Deterministic encryption**: the output of `Enc` at every parameter and on every input
does not depend on its coins (the hypothesis of [PS10, Theorem 94.2]; statelessness is built
into the model, an `NUPPT` keeping no state between activations). -/
def Deterministic (S : PrivateKeyScheme) : Prop :=
  ∀ n (y : List Bool) (r r' : S.enc.Coins n), S.enc.runAt n y r = S.enc.runAt n y r'

/-- Unfolding of the ciphertext sampler. -/
theorem encDist_apply (S : PrivateKeyScheme) (n : ℕ) (m : Fin n → Bool)
    (r : S.gen.Coins n × S.enc.Coins n) :
    S.encDist n m r = S.enc.runAt n (pairEncode (S.gen.runAt n [] r.1) (List.ofFn m)) r.2 := rfl

/-- Unfolding of the list encoding on a cons. -/
theorem encodeList_cons (m : List Bool) (ms : List (List Bool)) :
    encodeList (m :: ms) = pairEncode m (encodeList ms) := rfl

/-- The first two components of the encoding of a tuple with at least two entries. -/
theorem firstTwo_encodeList_ofFn {k : ℕ} (hk : 1 < k) (f : Fin k → List Bool) :
    pairFstD (encodeList (List.ofFn f)) = f ⟨0, by omega⟩ ∧
      pairFstD (pairSndD (encodeList (List.ofFn f))) = f ⟨1, hk⟩ := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  simp [List.ofFn_succ, encodeList]

/-- **Multi-message security implies single-message security** (the sanity direction of
[PS10, §3.7]: Definition 93.1 "extends" Definition 91.1, the case `q = 0` of one message).

**Proof sketch.** Given `D`, let `B` be the machine `NUPPT.exists_comp D` with
`pre := pairFstD` and `post := id`: `B(1^n, ⟨c, []⟩; r) = D(1^n, c; r)`. For `q := const 0`
the vector `fun _ => m` has `multiEncDist n 0 (fun _ => m) r = encodeList [Enc_k(m; r.2 0)]`
(`List.ofFn_succ`, `encodeList`), so `B.distinguisherL n` on it is `D.distinguisherL n` on
`encDist n m (r.1, r.2 0)` (`pairFstD_pairEncode`). The hypothesis at `B`, `const 0` gives a
negligible `ε`; at `n, m₀, m₁` the two advantages agree after relabelling the seeds by
`S.gen.Coins n × (Fin 1 → S.enc.Coins n) ≃ S.gen.Coins n × S.enc.Coins n`
(`Equiv.funUnique`, `acceptProb_comp_equiv`) and the coins by `B.coins = D.coins`
(`acceptProb_distinguisherL_congr`). -/
theorem MultiMessageSecure.singleMessageSecure {S : PrivateKeyScheme} (h : S.MultiMessageSecure) :
    S.SingleMessageSecure := by
  intro D
  obtain ⟨B, hBc, -, -, hB⟩ := D.exists_comp polyTimeComputable_pairFstD polyTimeComputable_id
  obtain ⟨ε, hε, hD⟩ := h B (.const 0)
  refine ⟨ε, hε, fun n m₀ m₁ => ?_⟩
  -- the verdict of `B` on the one-ciphertext vector is the verdict of `D` on the ciphertext
  have key : ∀ m : Fin n → Bool,
      acceptProb (S.multiEncDist n ((PolyExpr.const 0).eval n) (fun _ => m)) (B.distinguisherL n) =
        acceptProb (S.encDist n m) (D.distinguisherL n) := by
    intro m
    have h1 := acceptProb_distinguisherL_congr hBc n
      (S.multiEncDist n ((PolyExpr.const 0).eval n) (fun _ => m))
      (fun r => S.encDist n m (r.1, r.2 0)) (fun r c => by
        have e : pairFstD (S.multiEncDist n ((PolyExpr.const 0).eval n) (fun _ => m) r) =
            S.encDist n m (r.1, r.2 0) := by
          simp [multiEncDist, encDist, encodeList, List.ofFn_succ]
        rw [hB, e]
        rfl)
    rw [h1]
    exact acceptProb_comp_equiv
      ((Equiv.refl (S.gen.Coins n)).prodCongr
        (@Equiv.funUnique (Fin ((PolyExpr.const 0).eval n + 1)) (S.enc.Coins n)
          (inferInstanceAs (Unique (Fin 1)))))
      (S.encDist n m) (D.distinguisherL n)
  have := hD n (fun _ => m₀) (fun _ => m₁)
  unfold distAdv at this ⊢
  rwa [key m₀, key m₁] at this

end PrivateKeyScheme

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
  simp [padXor, Fin.castLE]

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
  change |acceptProb (fun s => padXor h m₀ (G s)) D - acceptProb (fun s => padXor h m₁ (G s)) D| ≤
    |acceptProb (fun s => padXor h m₀ (G s)) D - acceptProb (fun p => padXor h m₀ p) D| +
    |acceptProb (fun s => padXor h m₁ (G s)) D - acceptProb (fun p => padXor h m₁ p) D|
  rw [← e, abs_sub_comm (acceptProb (fun s => padXor h m₁ (G s)) D)]
  exact abs_sub_le _ _ _

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
  simp [prgPadFun, Function.comp]

/-- The activation of the pad machine on `⟨k, w⟩` is `w ⊕ F(k)`. -/
theorem runAt_prgPad {F : List Bool → List Bool} (hF : PolyTimeComputable F) (coins : PolyExpr)
    (n : ℕ) (k w : List Bool)
    (r : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prgPadFun hF) coins).Coins n) :
    (NUPPT.ofPolyTimeUniform (polyTimeComputable_prgPadFun hF) coins).runAt n (pairEncode k w) r =
      List.zipWith xor w (F k) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [prgPadFun, NUPPT.inArg, NUPPT.advInput]

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
    exact (P.expands n).le

/-- **The ciphertext distribution of Algorithm 92.1** is `m ⊕ G(k)|_n` for a uniform seed `k`
(the encryption coins are unused): `encDist n m (k, _) = ofFn (padXor m (G n k))`. -/
theorem prgScheme_encDist (P : PRG) (F : List Bool → List Bool) (hF : PolyTimeComputable F)
    (hG : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)) (n : ℕ)
    (m : Fin n → Bool) (r : (prgScheme P F hF hG).gen.Coins n × (prgScheme P F hF hG).enc.Coins n) :
    (prgScheme P F hF hG).encDist n m r = List.ofFn (padXor (P.expands n).le m (P.G n r.1)) := by
  show (NUPPT.ofPolyTimeUniform (polyTimeComputable_prgPadFun hF) (.const 0)).runAt n
    (pairEncode ((NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var).runAt n [] r.1)
      (List.ofFn m)) r.2 = _
  rw [runAt_coinKey, runAt_prgPad hF, hG]
  exact zipWith_xor_ofFn (P.expands n).le m (P.G n r.1)

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
    { toFun := fun z => ((z.1, fun i => Fin.elim0 i), z.2)
      invFun := fun z => (z.1.1, z.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => Prod.ext (Prod.ext rfl (funext fun i => Fin.elim0 i)) rfl }
  unfold acceptProb
  rw [← uprob_comp_equiv e]
  congr 1
  funext z
  simp only [e, Equiv.coe_fn_mk, prgScheme_encDist]

/-- **A machine that runs `D` on `m ⊕ t` is the distinguisher `D ∘ (m ⊕ ·)`**: if
`B(1^n, t; r) = D(1^n, m ⊕ t|_n; r)` for every `L`-bit string `t` (with `B.coins = D.coins`),
then the PRG advantage of `B` as a typed distinguisher of `L`-bit strings equals the PRG
advantage of `D ∘ (m ⊕ ·)` — the machine form of the hybrid distinguishers of
[PS10, Theorem 92.2, proof] (`acceptProb_distinguisherL_congr` on both terms of `prgAdv`). -/
private theorem prgAdv_eq_of_runAtL {n L : ℕ} (h : n ≤ L) {B D : NUPPT} (hc : B.coins = D.coins)
    (m : Fin n → Bool) {σ : Type*} [Fintype σ] (G : σ → Fin L → Bool)
    (hB : ∀ (t : Fin L → Bool) r,
      B.runAtL n (List.ofFn t) r = D.runAtL n (List.ofFn (padXor h m t)) r) :
    prgAdv G (fun t r => D.distinguisherL n (List.ofFn (padXor h m t)) r) =
      prgAdv G (B.distinguisher n L) := by
  unfold prgAdv distAdv
  have e₁ : acceptProb G (B.distinguisher n L) =
      acceptProb (fun s => List.ofFn (G s)) (B.distinguisherL n) := rfl
  have e₂ : acceptProb id (B.distinguisher n L) =
      acceptProb (fun t : Fin L → Bool => List.ofFn t) (B.distinguisherL n) := rfl
  rw [e₁, e₂,
    acceptProb_distinguisherL_congr hc n _ (fun s => List.ofFn (padXor h m (G s)))
      (fun s r => hB (G s) r),
    acceptProb_distinguisherL_congr hc n _ (fun t => List.ofFn (padXor h m t)) (fun t r => hB t r)]
  rfl

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
along `Bᵢ.coins = D.coins` (`prgAdv_eq_of_runAtL`, `acceptProb_distinguisherL_congr`).
Asymptotic step:
`ν n := prgAdv (G n) (B₀.distinguisher n (ℓ n)) + prgAdv (G n) (B₁.distinguisher n (ℓ n))` is
negligible by `PRG.secure_iff` applied to `hP` and `Negligible.add`; by maximality
`distAdv (encDist n m₀) (encDist n m₁) (D.distinguisherL n) ≤ ν n` for every `n, m₀, m₁`, so
`ε := ν` witnesses `SingleMessageSecure`. -/
theorem prgScheme_singleMessageSecure (P : PRG) (hP : P.Secure) (F : List Bool → List Bool)
    (hF : PolyTimeComputable F) (hG : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)) :
    (prgScheme P F hF hG).SingleMessageSecure := by
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
    simp [Function.comp]
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
    prgAdv (P.G n) (B₁.distinguisher n (P.stretch.eval n)), (hP.2 B₀).add (hP.2 B₁),
    fun n m₀ m₁ => ?_⟩
  refine (hμ n (m₀, m₁)).trans ?_
  unfold distAdv
  dsimp only
  rw [acceptProb_prgScheme_encDist, acceptProb_prgScheme_encDist,
    ← prgAdv_eq_of_runAtL (P.expands n).le (hB₀c.trans hD'c) (μ n).1 (P.G n) (hrun B₀ _ hB₀ n),
    ← prgAdv_eq_of_runAtL (P.expands n).le (hB₁c.trans hD'c) (μ n).2 (P.G n) (hrun B₁ _ hB₁ n)]
  exact distAdv_padXor_le (P.expands n).le (P.G n) (μ n).1 (μ n).2
    (fun t r => D.distinguisherL n (List.ofFn t) r)

/-! ### Deterministic schemes are not multi-message secure [PS10, Theorem 94.2] -/

namespace PrivateKeyScheme

/-- The raw string function of the distinguisher of [PS10, Theorem 94.2]: on the layout
`⟨⟨⟨1^n, w⟩, α⟩, r⟩` with `w = ⟨c₀, ⟨c₁, …⟩⟩`, output `[c₀ = c₁]`. -/
def firstTwoEqFun (z : List Bool) : List Bool :=
  [decide (pairFstD (NUPPT.inArg z) = pairFstD (pairSndD (NUPPT.inArg z)))]

/-- `firstTwoEqFun` is polynomial-time: two projections and one string equality test
(`Complexity.polyTimeComputable_pairEq`). -/
theorem polyTimeComputable_firstTwoEqFun : PolyTimeComputable firstTwoEqFun := by
  have h := polyTimeComputable_pairEq.comp
    ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
      ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
        NUPPT.polyTimeComputable_inArg))
  convert h using 1
  funext z
  simp [firstTwoEqFun, Function.comp]

/-- The distinguisher `[c₀ = c₁]` accepts a word `w` iff its first two components agree. -/
theorem distinguisherL_firstTwoEq (coins : PolyExpr) (n : ℕ) (w : List Bool)
    (r : (NUPPT.ofPolyTimeUniform polyTimeComputable_firstTwoEqFun coins).Coins n) :
    (NUPPT.ofPolyTimeUniform polyTimeComputable_firstTwoEqFun coins).distinguisherL n w r = true ↔
      pairFstD w = pairFstD (pairSndD w) := by
  rw [NUPPT.distinguisherL, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [firstTwoEqFun, NUPPT.inArg, NUPPT.advInput]

/-- **[PS10, Theorem 94.2]: a deterministic (stateless) encryption scheme is not
multi-message secure.** The text's argument: for messages `m₀ ≠ m₁`, the encryptions
`(c₀, c₁)` of `(m₀, m₀)` satisfy `c₀ = c₁` when `Enc` is deterministic, while the encryptions
`(c'₀, c'₁)` of `(m₀, m₁)` satisfy `c'₀ ≠ c'₁` (otherwise `Dec_k` would recover both `m₀` and
`m₁` from the same ciphertext, contradicting correctness); the PPT distinguisher `[c₀ = c₁]`
(`firstTwoEqFun`, with `q := const 1`, two messages) therefore has advantage exactly `1` at
every `n ≥ 1`, which no negligible `ε` bounds.

**Deviation:** the proof uses correctness (to get `c'₀ ≠ c'₁`) and `n ≥ 1` (two distinct
messages), both implicit in the text; "stateless" is built into the model.

**Proof sketch.** Assume multi-message security and apply it to the machine
`ofPolyTimeUniform polyTimeComputable_firstTwoEqFun` (no coins) and `q := const 1`, obtaining
a negligible `ε`; pick `n := n₀ + 1` with `|ε n| < 1` (the case `c = 1` of negligibility).
With `m₀ := 0^n`, `m₁ := 1^n` (distinct at index `0`), compare the vectors `v = (m₀, m₀)` and
`v' = (m₀, m₁)`. The verdict of the machine on `multiEncDist n 1 w r` is the equality of the
first two ciphertexts (`distinguisherL_firstTwoEq`, `firstTwo_encodeList_ofFn`). On `v` the
two ciphertexts are the same deterministic function of `(k, m₀)` (`hS`), so the acceptance
probability is `1` (`uprob_true`); on `v'` equal ciphertexts would give
`some m₀ = Dec_k(c'₀) = Dec_k(c'₁) = some m₁` by `S.correct`, so the acceptance probability is
`0` (`uprob_false`). Hence `distAdv = 1 ≤ ε n`, contradicting `|ε n| < 1`. -/
theorem not_multiMessageSecure_of_deterministic (S : PrivateKeyScheme) (hS : S.Deterministic) :
    ¬ S.MultiMessageSecure := by
  intro hsec
  obtain ⟨ε, hε, hD⟩ :=
    hsec (NUPPT.ofPolyTimeUniform polyTimeComputable_firstTwoEqFun (.const 0)) (.const 1)
  obtain ⟨n₀, hn₀⟩ := hε 1
  -- the parameter `n = n₀ + 1 ≥ 1` at which `ε n < 1`
  have hεn : |ε (n₀ + 1)| < 1 := by
    have h := hn₀ (n₀ + 1) (Nat.le_succ n₀)
    have h1 : (1 : ℝ) / ((n₀ + 1 : ℕ) : ℝ) ^ 1 ≤ 1 := by
      rw [pow_one]
      exact div_le_one_of_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n₀))
        (by positivity)
    linarith
  -- two distinct messages and the two message vectors `(m₀, m₀)` and `(m₀, m₁)`
  set n := n₀ + 1 with hn
  let m₀ : Fin n → Bool := fun _ => false
  let m₁ : Fin n → Bool := fun _ => true
  have hm : m₀ ≠ m₁ := fun h => by
    have := congrFun h ⟨0, by omega⟩
    simp [m₀, m₁] at this
  have h0 : 0 < (PolyExpr.const 1).eval n + 1 := Nat.succ_pos _
  have h1 : 1 < (PolyExpr.const 1).eval n + 1 := by simp
  let v : Fin ((PolyExpr.const 1).eval n + 1) → Fin n → Bool := fun _ => m₀
  let v' : Fin ((PolyExpr.const 1).eval n + 1) → Fin n → Bool :=
    fun i => if i.val = 0 then m₀ else m₁
  have hadv := hD n v v'
  -- the verdict on a two-message encryption is the equality of the two ciphertexts
  have hacc : ∀ w : Fin ((PolyExpr.const 1).eval n + 1) → Fin n → Bool,
      acceptProb (S.multiEncDist n ((PolyExpr.const 1).eval n) w)
        ((NUPPT.ofPolyTimeUniform polyTimeComputable_firstTwoEqFun (.const 0)).distinguisherL n) =
      uprob fun z : (S.gen.Coins n × (Fin ((PolyExpr.const 1).eval n + 1) → S.enc.Coins n)) ×
          (NUPPT.ofPolyTimeUniform polyTimeComputable_firstTwoEqFun (.const 0)).Coins n =>
        S.enc.runAt n (pairEncode (S.gen.runAt n [] z.1.1) (List.ofFn (w ⟨0, h0⟩))) (z.1.2 ⟨0, h0⟩) =
          S.enc.runAt n (pairEncode (S.gen.runAt n [] z.1.1) (List.ofFn (w ⟨1, h1⟩)))
            (z.1.2 ⟨1, h1⟩) := by
    intro w
    unfold acceptProb
    congr 1
    funext z
    rw [distinguisherL_firstTwoEq, multiEncDist]
    obtain ⟨h₁, h₂⟩ := firstTwo_encodeList_ofFn h1 fun i =>
      S.enc.runAt n (pairEncode (S.gen.runAt n [] z.1.1) (List.ofFn (w i))) (z.1.2 i)
    rw [h₁, h₂]
  -- on `(m₀, m₀)` the two ciphertexts agree: acceptance probability `1`
  have hone : acceptProb (S.multiEncDist n ((PolyExpr.const 1).eval n) v)
      ((NUPPT.ofPolyTimeUniform polyTimeComputable_firstTwoEqFun (.const 0)).distinguisherL n) = 1 := by
    rw [hacc]
    have : (fun z : (S.gen.Coins n × (Fin ((PolyExpr.const 1).eval n + 1) → S.enc.Coins n)) ×
          (NUPPT.ofPolyTimeUniform polyTimeComputable_firstTwoEqFun (.const 0)).Coins n =>
        S.enc.runAt n (pairEncode (S.gen.runAt n [] z.1.1) (List.ofFn (v ⟨0, h0⟩))) (z.1.2 ⟨0, h0⟩) =
          S.enc.runAt n (pairEncode (S.gen.runAt n [] z.1.1) (List.ofFn (v ⟨1, h1⟩)))
            (z.1.2 ⟨1, h1⟩)) = fun _ => True := by
      funext z
      exact propext ⟨fun _ => trivial, fun _ => hS n _ _ _⟩
    rw [this, uprob_true]
  -- on `(m₀, m₁)` the two ciphertexts differ (by correctness): acceptance probability `0`
  have hzero : acceptProb (S.multiEncDist n ((PolyExpr.const 1).eval n) v')
      ((NUPPT.ofPolyTimeUniform polyTimeComputable_firstTwoEqFun (.const 0)).distinguisherL n) = 0 := by
    rw [hacc]
    have : (fun z : (S.gen.Coins n × (Fin ((PolyExpr.const 1).eval n + 1) → S.enc.Coins n)) ×
          (NUPPT.ofPolyTimeUniform polyTimeComputable_firstTwoEqFun (.const 0)).Coins n =>
        S.enc.runAt n (pairEncode (S.gen.runAt n [] z.1.1) (List.ofFn (v' ⟨0, h0⟩))) (z.1.2 ⟨0, h0⟩) =
          S.enc.runAt n (pairEncode (S.gen.runAt n [] z.1.1) (List.ofFn (v' ⟨1, h1⟩)))
            (z.1.2 ⟨1, h1⟩)) = fun _ => False := by
      funext z
      refine propext ⟨fun heq => ?_, fun h => h.elim⟩
      have hv0 : v' ⟨0, h0⟩ = m₀ := by simp [v']
      have hv1 : v' ⟨1, h1⟩ = m₁ := by simp [v']
      rw [hv0, hv1] at heq
      have c₀ := S.correct n m₀ z.1.1 (z.1.2 ⟨0, h0⟩) (fun _ => false)
      have c₁ := S.correct n m₁ z.1.1 (z.1.2 ⟨1, h1⟩) (fun _ => false)
      rw [heq, c₁, Option.some.injEq] at c₀
      exact hm c₀.symm
    rw [this, uprob_false]
  -- the advantage is `1`, but `ε n < 1`
  rw [distAdv, hone, hzero] at hadv
  have h1 : (1 : ℝ) ≤ ε n := by simpa using hadv
  linarith [le_abs_self (ε n)]

end PrivateKeyScheme

end TCSlib.Cryptography
