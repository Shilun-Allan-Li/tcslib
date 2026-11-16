/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Encryption.PrivateKey.Scheme
import TCSlib.Cryptography.Foundations.Negligible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Private-key ensemble security

The adversary receives a ciphertext or a fixed vector of ciphertexts, together with the
security parameter. The vector uses one key and independent encryption coins. Its
polynomially many ciphertexts are encoded as nested pairs.

## Main definitions

* `PrivateKeyScheme.encDist` and `PrivateKeyScheme.multiEncDist` sample the ciphertexts.
* `PrivateKeyScheme.SingleMessageSecure` and `PrivateKeyScheme.MultiMessageSecure` express
  negligible distinguishing advantage [PS10, Definitions 91.1 and 93.1].
* `PrivateKeyScheme.Deterministic` says encryption ignores its coins.

## Main results

* `PrivateKeyScheme.MultiMessageSecure.singleMessageSecure` reduces the single-message
  game to the vector game [PS10, §3.7].
* `PrivateKeyScheme.not_multiMessageSecure_of_deterministic` uses a two-message
  distinguisher to rule out security for stateless deterministic schemes
  [PS10, Theorem 94.2].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.5, Definition 91.1, and §3.7, Definition 93.1 and Theorem 94.2.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

namespace PrivateKeyScheme

/-! ### Transporting a distinguisher along an equality of coin polynomials -/

/-- **Transport of a distinguisher along `A.coins = B.coins`**: if the activations of `A` on
`X s` and of `B` on `Y s` agree for every seed `s` and every coin string, then the acceptance
probabilities of `A` on `X` and of `B` on `Y` agree. The coin types `A.Coins n` and
`B.Coins n` are identified by `finCongr` (`List.ofFn_congr`) and the seed spaces relabelled
by `uprob_comp_equiv`. This is the bridge by which a machine obtained from the closure
calculus (`Complexity.NUPPT.exists_comp`, `NUPPT.exists_withAdvice`) is compared with the
given adversary. -/
theorem acceptProb_distinguisherL_congr {σ : Type*} [Fintype σ] {A B : NUPPT}
    (hc : A.coins = B.coins) (n : ℕ) (X Y : σ → List Bool)
    (h : ∀ s r, A.runAtL n (X s) r = B.runAtL n (Y s) r) :
    acceptProb X (A.distinguisherL n) = acceptProb Y (B.distinguisherL n) := by
  have hlen : A.coinLen n = B.coinLen n := by simp only [NUPPT.coinLen_eq, hc]
  let e : A.Coins n ≃ B.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  have hofn : ∀ r : A.Coins n, List.ofFn (e r) = List.ofFn r := fun r =>
    (List.ofFn_congr hlen r).symm
  simp only [acceptProb_def]
  have := uprob_comp_equiv ((Equiv.refl σ).prodCongr e)
    (fun z : σ × B.Coins n => B.distinguisherL n (Y z.1) z.2 = true)
  rw [← this]
  congr 1
  funext z
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply,
    NUPPT.distinguisherL_eq, NUPPT.runAt_eq, h, hofn]

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

/-- The defining property of `SingleMessageSecure`: every distinguisher has a negligible bound
`ε` on its advantage between the encryptions of any two messages. -/
theorem singleMessageSecure_iff (S : PrivateKeyScheme) : S.SingleMessageSecure ↔
    ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (m₀ m₁ : Fin n → Bool),
      distAdv (S.encDist n m₀) (S.encDist n m₁) (D.distinguisherL n) ≤ ε n :=
  Iff.rfl

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

/-- Unfolding of the list encoding on the empty list: `encodeList [] = []`. -/
theorem encodeList_nil : encodeList [] = [] := rfl

/-- Unfolding of the multi-message ciphertext sampler: the `encodeList` of the `q + 1`
encryptions `Enc(1^n, ⟨k, m_i⟩; s_i)` under the key `k = Gen(1^n; r.1)`, `s_i = r.2 i`. -/
theorem multiEncDist_apply (S : PrivateKeyScheme) (n q : ℕ) (m : Fin (q + 1) → Fin n → Bool)
    (r : S.gen.Coins n × (Fin (q + 1) → S.enc.Coins n)) :
    S.multiEncDist n q m r = encodeList (List.ofFn fun i =>
      S.enc.runAt n (pairEncode (S.gen.runAt n [] r.1) (List.ofFn (m i))) (r.2 i)) := rfl

/-- The defining property of `MultiMessageSecure`: for every `D` and `q` some negligible `ε`
bounds `D`'s advantage between the encryptions of any two message vectors `m, m'` of
`q(n) + 1` messages under one key. -/
theorem multiMessageSecure_iff (S : PrivateKeyScheme) :
    S.MultiMessageSecure ↔ ∀ (D : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (m m' : Fin (q.eval n + 1) → Fin n → Bool),
        distAdv (S.multiEncDist n (q.eval n) m) (S.multiEncDist n (q.eval n) m')
          (D.distinguisherL n) ≤ ε n := Iff.rfl

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
  simp only [distAdv_def] at this ⊢
  rwa [key m₀, key m₁] at this

end PrivateKeyScheme

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
  simp [firstTwoEqFun, Function.comp_apply]

/-- The distinguisher `[c₀ = c₁]` accepts a word `w` iff its first two components agree. -/
theorem distinguisherL_firstTwoEq (coins : PolyExpr) (n : ℕ) (w : List Bool)
    (r : (NUPPT.ofPolyTimeUniform polyTimeComputable_firstTwoEqFun coins).Coins n) :
    (NUPPT.ofPolyTimeUniform polyTimeComputable_firstTwoEqFun coins).distinguisherL n w r = true ↔
      pairFstD w = pairFstD (pairSndD w) := by
  rw [NUPPT.distinguisherL_eq, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [firstTwoEqFun, NUPPT.inArg_eq, NUPPT.advInput_eq]

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
  obtain ⟨n₀, hn₀⟩ := (negligible_iff ε).1 hε 1
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
    simp only [acceptProb_def]
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
  rw [distAdv_def, hone, hzero] at hadv
  have h1 : (1 : ℝ) ≤ ε n := by simpa using hadv
  linarith [le_abs_self (ε n)]

end PrivateKeyScheme

end TCSlib.Cryptography
