/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
import TCSlib.Cryptography.HardcoreBit.Basic
import Mathlib.Algebra.Ring.BooleanRing

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The finite PRF encryption hybrid

The outer switches use PRF advantage. The inner switches replace random-function
answers at sampled points by independent pads, with a loss bounded by the probability
of repeated points. The two independent-pad experiments agree by perfect secrecy.

## Main definitions

* `chainTree` asks a fixed tuple of oracle queries.
* `prfEncReal` and `otpEnc` sample the ciphertext tuples in the real and independent-pad experiments.
* `multiMsgAdv` runs a tuple distinguisher after querying the oracle at the sampled points.

## Main results

* `prfAdv_multiMsgAdv` identifies the outer switch with a PRF advantage.
* `distAdv_prfEncReal_random_otp_le` bounds the inner switch by the collision probability.
* `acceptProb_otpEnc` equates the two independent-pad experiments.
* `distAdv_prfEncReal_le` combines the switches [PS10, Theorem 99.2, proof].

**Deviation.** The vector has `q + 1` points, giving collision term `C(q + 1, 2) / 2^n`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.7, Definition 93.1, and §3.9, Algorithm 99.1 and Theorem 99.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (oracle adversaries and PRF advantage).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Query chains -/

/-- The query tree that asks the fixed tuple of queries `xs : Fin k → I` in order and then
outputs `f` applied to the tuple of answers: `k` `query` nodes in a chain. -/
def chainTree {I O α : Type} : ∀ (k : ℕ), (Fin k → I) → ((Fin k → O) → α) → QueryTree I O α
  | 0, _, f => .ret (f Fin.elim0)
  | k + 1, xs, f => .query (xs 0) fun o => chainTree k (Fin.tail xs) fun os => f (Fin.cons o os)

/-- Running a query chain against the oracle `g` outputs `f` of the tuple of answers
`g (xs j)`. -/
theorem eval_chainTree {I O α : Type} (g : I → O) :
    ∀ (k : ℕ) (xs : Fin k → I) (f : (Fin k → O) → α),
      (chainTree k xs f).eval g = f fun j => g (xs j)
  | 0, xs, f => by
    simp only [chainTree, QueryTree.eval_ret]
    congr
    funext j
    exact j.elim0
  | k + 1, xs, f => by
    simp only [chainTree, QueryTree.eval_query]
    rw [eval_chainTree g k]
    congr
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp [Fin.tail_def]

/-- A chain of `k` queries makes at most `k` queries. -/
theorem boundedBy_chainTree {I O α : Type} :
    ∀ (k : ℕ) (xs : Fin k → I) (f : (Fin k → O) → α), (chainTree k xs f).BoundedBy k
  | 0, _, _ => by
    rw [chainTree]
    exact QueryTree.boundedBy_ret _ _
  | k + 1, xs, f => by
    rw [chainTree, QueryTree.boundedBy_query_succ]
    exact fun o => boundedBy_chainTree k (Fin.tail xs) fun os => f (Fin.cons o os)

/-! ### The hybrids of [PS10, Theorem 99.2], concrete -/

section Concrete

variable {n q : ℕ} {K ρ : Type*} [Fintype K] [Fintype ρ]

/-- The ciphertext tuple `(r_j, m_j ⊕ F(r_j))_{j ≤ q}` for a key `z.1 : K` and the points
`z.2 : Fin (q+1) → {0,1}^n`, with `F : K → {0,1}^n → {0,1}^n`. With `F` the PRF this is the
hybrid `H¹` ("real encryptions"); with `F = randomFunction` (keys are function tables) it is
`H²` ("replace `f` with a truly random function `R`") of [PS10, Theorem 99.2, proof]. -/
def prfEncReal (F : K → (Fin n → Bool) → (Fin n → Bool)) (m : Fin (q + 1) → Fin n → Bool) :
    K × (Fin (q + 1) → Fin n → Bool) → (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :=
  fun z j => (z.2 j, m j + F z.1 (z.2 j))

omit [Fintype K] in
/-- The hybrid ciphertext at position `j` contains the point `z.2 j` and the message
masked with the oracle's value at that point [PS10, Theorem 99.2, proof]. -/
theorem prfEncReal_apply (F : K → (Fin n → Bool) → (Fin n → Bool)) (m : Fin (q + 1) → Fin n → Bool)
    (z : K × (Fin (q + 1) → Fin n → Bool)) (j : Fin (q + 1)) :
    prfEncReal F m z j = (z.2 j, m j + F z.1 (z.2 j)) := rfl

/-- The ciphertext tuple `(r_j, m_j ⊕ p_j)_{j ≤ q}` with independent uniform pads `p_j`: the
hybrid `H³` ("using OTP") of [PS10, Theorem 99.2, proof]; seeds `(r, p)`. -/
def otpEnc (m : Fin (q + 1) → Fin n → Bool) :
    (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin n → Bool) →
      (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :=
  fun z j => (z.1 j, m j + z.2 j)

/-- **The oracle adversary of Thm-99.2.1** ([PS10, Theorem 99.2, proof, "`H¹` and `H²` …
otherwise (by closure under efficient operations) we contradict the pseudorandomness property"]):
on coins `(r, c)` it queries its oracle at `r₀, …, r_q` (a chain of `q + 1` queries), forms the
tuple `(r_j, m_j ⊕ ans_j)_j` and runs the distinguisher `D` on it with coins `c`. The messages
`m` are hard-wired (non-uniform advice in the machine version). -/
def multiMsgAdv (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    OracleAdversary ((Fin (q + 1) → Fin n → Bool) × ρ) (Fin n → Bool) (Fin n → Bool) :=
  fun c => chainTree (q + 1) c.1 fun ans => D (fun j => (c.1 j, m j + ans j)) c.2

omit [Fintype ρ] in
/-- Evaluating the hybrid adversary on an oracle runs the tuple distinguisher on the sampled
points and the messages masked by the oracle values [PS10, Theorem 99.2, proof]. -/
theorem eval_multiMsgAdv (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool)
    (g : (Fin n → Bool) → Fin n → Bool) (c : (Fin (q + 1) → Fin n → Bool) × ρ) :
    (multiMsgAdv m D c).eval g = D (fun j => (c.1 j, m j + g (c.1 j))) c.2 := by
  rw [multiMsgAdv, eval_chainTree]

omit [Fintype ρ] in
/-- `multiMsgAdv m D` makes at most `q + 1` queries. -/
theorem multiMsgAdv_boundedBy (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    (multiMsgAdv m D).BoundedBy (q + 1) :=
  (OracleAdversary.boundedBy_iff _ _).2 fun c => boundedBy_chainTree (q + 1) c.1 _

/-- Running `multiMsgAdv m D` with the oracle `F k` (for a uniform key `k`) accepts with the
probability that `D` accepts the hybrid sampler `prfEncReal F m` (reassociation of the seed
space `K × (points × coins)`). -/
theorem acceptProb_oracleDist_multiMsgAdv (F : K → (Fin n → Bool) → (Fin n → Bool))
    (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    acceptProb F (oracleDist (multiMsgAdv m D)) = acceptProb (prfEncReal F m) D := by
  rw [acceptProb_def, acceptProb_def]
  rw [← uprob_comp_equiv (Equiv.prodAssoc K (Fin (q + 1) → Fin n → Bool) ρ)]
  congr 1
  funext z
  simp only [oracleDist_apply, multiMsgAdv, eval_chainTree, Equiv.prodAssoc_apply]
  rfl

/-- **Thm-99.2.1: the gap `H¹ → H²` is a PRF advantage.** The advantage of `D` between the real
encryptions `(r_j, m_j ⊕ F_k(r_j))_j` and the random-function encryptions
`(r_j, m_j ⊕ R(r_j))_j` is exactly the PRF advantage of the `(q+1)`-query oracle adversary
`multiMsgAdv m D` against `F` (unfolding of `prfAdv`, `oracleDist` and `acceptProb`). -/
theorem prfAdv_multiMsgAdv (F : K → (Fin n → Bool) → (Fin n → Bool))
    (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    prfAdv F (multiMsgAdv m D) =
      distAdv (prfEncReal F m) (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) D := by
  rw [prfAdv_def, distAdv_def, distAdv_def, acceptProb_oracleDist_multiMsgAdv,
    acceptProb_oracleDist_multiMsgAdv]

/-- **The collision bound** ([PS10, Theorem 99.2, proof, "`∃ i, j` such that `r_i = r_j`, but this
happens only with probability `C(q,2) · 2^{−n}`"]): `q + 1` uniform `n`-bit points fail to be
pairwise distinct with probability at most `C(q+1, 2) / 2^n`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** `¬ Injective r ↔ ∃ (i, j) with i < j, r i = r j`; the union bound
`uprob_exists_le` over the `C(q+1, 2)` pairs `i < j` (`Finset.card_filter` of `univ.filter (i < j)`
on `Fin (q+1) × Fin (q+1)`, `Fin.card_filter_lt`/`Nat.choose_two_right`-style counting); for
`i ≠ j` the pair `(r i, r j)` is uniform on `({0,1}^n)²` (`HardcoreBit.pushesUniform_eval_pair`),
so `uprob (r i = r j) = uprob (fun (a, b) => a = b) = 2^n / 4^n = 1 / 2^n`
(`PushesUniform.uprob_eq`, `uprob_eq_card_filter`, `Fintype.card_fun`, `Fintype.card_bool`). -/
theorem uprob_not_injective_le :
    uprob (fun r : Fin (q + 1) → Fin n → Bool => ¬ Function.Injective r) ≤
      (Nat.choose (q + 1) 2 : ℝ) / 2 ^ n := by
  classical
  set S : Finset (Fin (q + 1) × Fin (q + 1)) := univ.filter fun p => p.1 < p.2 with hS
  -- a collision is a pair `i < j` with `r i = r j`
  have h1 : uprob (fun r : Fin (q + 1) → Fin n → Bool => ¬ Function.Injective r) ≤
      uprob (fun r : Fin (q + 1) → Fin n → Bool => ∃ p ∈ S, r p.1 = r p.2) := by
    refine uprob_mono fun r hr => ?_
    rw [Function.not_injective_iff] at hr
    obtain ⟨i, j, hij, hne⟩ := hr
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨(i, j), by simp [S, h], hij⟩
    · exact ⟨(j, i), by simp [S, h], hij.symm⟩
  -- each pair `i < j` collides with probability `2^{-n}`
  have h3 : ∀ p ∈ S, uprob (fun r : Fin (q + 1) → Fin n → Bool => r p.1 = r p.2) = 1 / 2 ^ n := by
    intro p hp
    have hlt : p.1 < p.2 := by simpa [S] using hp
    have h : uprob (fun r : Fin (q + 1) → Fin n → Bool => r p.1 = r p.2) =
        uprob (fun z : (Fin n → Bool) × (Fin n → Bool) => z.1 = z.2) :=
      (HardcoreBit.pushesUniform_eval_pair (γ := Fin n → Bool) (ne_of_lt hlt)).uprob_eq
        (fun z : (Fin n → Bool) × (Fin n → Bool) => z.1 = z.2)
    rw [h, MultiMsg.uprob_eq_pair, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    simp
  -- the union bound over the `C(q+1, 2)` pairs
  have h2 := uprob_exists_le S (fun p (r : Fin (q + 1) → Fin n → Bool) => r p.1 = r p.2)
  rw [Finset.sum_congr rfl h3, Finset.sum_const, nsmul_eq_mul, hS,
    MultiMsg.card_filter_lt_pairs, mul_one_div] at h2
  exact h1.trans h2

/-- **A uniform table read at distinct points is uniform**: for an injective tuple of points
`r : Fin (q+1) → I`, the map `R ↦ (R (r j))_j` pushes the uniform distribution on tables
`I → O` forward to the uniform distribution on `Fin (q+1) → O` (the generalization of
`HardcoreBit.pushesUniform_eval_pair` from two points to `q + 1` points).

**Proof sketch.** For an empty `O` both averages are over empty types. Otherwise this is the
restriction along the injective `r` (`HardcoreBit.pushesUniform_restrict`). -/
theorem pushesUniform_comp_injective {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    {r : Fin (q + 1) → I} (hr : Function.Injective r) :
    HardcoreBit.PushesUniform (fun R : I → O => fun j => R (r j)) := by
  classical
  rcases isEmpty_or_nonempty O with hO | hO
  · -- no tables and no tuples: both averages are over empty types
    refine (HardcoreBit.pushesUniform_iff _).2 fun F => ?_
    haveI : IsEmpty (I → O) := ⟨fun R => hO.false (R (r 0))⟩
    haveI : IsEmpty (Fin (q + 1) → O) := ⟨fun f => hO.false (f 0)⟩
    simp only [uexp_def, univ_eq_empty, sum_empty, zero_div]
  · exact HardcoreBit.pushesUniform_restrict hr

/-- **Thm-99.2.2: the gap `H² → H³` is at most the collision probability**
([PS10, Theorem 99.2, proof, "`H²` and `H³` are 'almost' identical except for the case when
`∃ i, j` such that `r_i = r_j`"]): the advantage of `D` between the random-function encryptions
`(r_j, m_j ⊕ R(r_j))_j` and the one-time-pad encryptions `(r_j, m_j ⊕ p_j)_j` is at most
`C(q+1, 2) / 2^n`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** Write both acceptance probabilities as averages over the points `r`
(`uprob_prod` after `uprob_prod_comm`): `a(r) := Pr_R[D((r_j, m_j ⊕ R(r_j))_j) = 1]` and
`b(r) := Pr_p[D((r_j, m_j ⊕ p_j)_j) = 1]`. When `r` is injective, `(R(r_j))_j` is uniform
(`pushesUniform_comp_injective`, `PushesUniform.uprob_eq`), so `a(r) = b(r)`; otherwise
`|a(r) − b(r)| ≤ 1` (`uprob_nonneg`, `uprob_le_one`). Hence
`|E_r a − E_r b| ≤ E_r |a − b| ≤ E_r [¬ Injective r] = uprob (¬ Injective)` (`uexp` is monotone
and `|∑| ≤ ∑ |·|`, `uprob_eq_uexp_ite`), and `uprob_not_injective_le` bounds the last term. -/
theorem distAdv_prfEncReal_random_otp_le (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    distAdv (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) (otpEnc m) D ≤
      (Nat.choose (q + 1) 2 : ℝ) / 2 ^ n := by
  classical
  -- the acceptance probabilities conditioned on the points `r`
  let a : (Fin (q + 1) → Fin n → Bool) → ℝ := fun r =>
    uprob fun w : ((Fin n → Bool) → (Fin n → Bool)) × ρ =>
      D (fun j => (r j, m j + w.1 (r j))) w.2 = true
  let b : (Fin (q + 1) → Fin n → Bool) → ℝ := fun r =>
    uprob fun w : (Fin (q + 1) → Fin n → Bool) × ρ => D (fun j => (r j, m j + w.1 j)) w.2 = true
  have ha : acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) D =
      uexp a := by
    rw [acceptProb_def, show randomFunction (Fin n → Bool) (Fin n → Bool) = id from
      funext fun f => randomFunction_apply _ _ f]
    exact (uprob_comp_equiv ((Equiv.prodAssoc (Fin (q + 1) → Fin n → Bool)
      ((Fin n → Bool) → (Fin n → Bool)) ρ).symm.trans
        ((Equiv.prodComm _ _).prodCongr (Equiv.refl ρ))) _).symm.trans
      (by rw [uprob_prod]; rfl)
  have hb : acceptProb (otpEnc m) D = uexp b := by
    rw [acceptProb_def]
    exact (uprob_comp_equiv (Equiv.prodAssoc (Fin (q + 1) → Fin n → Bool)
      (Fin (q + 1) → Fin n → Bool) ρ).symm _).symm.trans (by rw [uprob_prod]; rfl)
  -- at injective points the table values are fresh uniform pads
  have hab : ∀ r : Fin (q + 1) → Fin n → Bool, Function.Injective r → a r = b r := by
    intro r hr
    exact ((pushesUniform_comp_injective (O := Fin n → Bool) hr).prodMap
      (HardcoreBit.pushesUniform_id (Ω := ρ))).uprob_eq
      (fun v : (Fin (q + 1) → Fin n → Bool) × ρ => D (fun j => (r j, m j + v.1 j)) v.2 = true)
  rw [distAdv_def, ha, hb]
  exact (MultiMsg.abs_uexp_sub_le_uprob a b (fun r => ¬ Function.Injective r)
    (fun r => ⟨uprob_nonneg _, uprob_le_one _⟩) (fun r => ⟨uprob_nonneg _, uprob_le_one _⟩)
    (fun r hr => hab r (not_not.mp hr))).trans uprob_not_injective_le

/-- **Thm-99.2.3: `H³ = H⁴` by the perfect secrecy of the one-time pad** ([PS10, Theorem 99.2,
proof, "`H³` and `H⁴` are identical by the perfect secrecy of the OTP"], the vector version of
Claim-92.a): for independent uniform pads `p_j`, the tuples `(r_j, m_j ⊕ p_j)_j` and
`(r_j, m'_j ⊕ p_j)_j` are identically distributed, so every distinguisher accepts them with the
same probability.

**Proof sketch.** The map `(r, p) ↦ (r, p ⊕ (m ⊕ m'))` is a bijection of the seed space
(`Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))`) carrying the sampler for `m'` to the
sampler for `m` (in the Boolean group `x + x = 0`); relabel by it (`acceptProb_comp_equiv`). -/
theorem acceptProb_otpEnc (m m' : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    acceptProb (otpEnc m) D = acceptProb (otpEnc m') D := by
  have key : ∀ z : (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin n → Bool),
      otpEnc m' ((Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))) z) = otpEnc m z := by
    intro z
    funext j
    simp only [otpEnc, Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.coe_addRight, Prod.map_fst,
      Prod.map_snd, id_eq, Pi.add_apply]
    refine Prod.ext rfl ?_
    funext i
    simp only [Pi.add_apply]
    cases m j i <;> cases m' j i <;> cases z.2 j i <;> rfl
  calc acceptProb (otpEnc m) D
      = acceptProb (fun z => otpEnc m'
          ((Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))) z)) D := by
        congr 1
        funext z
        exact (key z).symm
    _ = acceptProb (otpEnc m') D := acceptProb_comp_equiv _ (otpEnc m') D

/-- **[PS10, Theorem 99.2], concrete form: the six-hybrid bound.** For a keyed family
`F : K → {0,1}^n → {0,1}^n`, message vectors `m, m' ∈ ({0,1}^n)^{q+1}` and any distinguisher
`D` of ciphertext tuples, the advantage of `D` between the real encryptions of `m` and of `m'`
is at most `prfAdv F (A_m D) + prfAdv F (A_{m'} D) + 2 · C(q+1, 2) / 2^n`, where `A_m D` is the
`(q+1)`-query oracle adversary `multiMsgAdv m D`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** Hybrids `H¹ = prfEncReal F m`, `H² = prfEncReal R m`, `H³ = otpEnc m`,
`H⁴ = otpEnc m'`, `H⁵ = prfEncReal R m'`, `H⁶ = prfEncReal F m'`: `|H¹ − H²|` and `|H⁵ − H⁶|` are
the two PRF advantages (`prfAdv_multiMsgAdv`), `|H² − H³|` and `|H⁴ − H⁵|` are at most the
collision bound (`distAdv_prfEncReal_random_otp_le`), `H³ = H⁴` (`acceptProb_otpEnc`); the
triangle inequality (`abs_sub_le`, five times) finishes. -/
theorem distAdv_prfEncReal_le (F : K → (Fin n → Bool) → (Fin n → Bool))
    (m m' : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    distAdv (prfEncReal F m) (prfEncReal F m') D ≤
      prfAdv F (multiMsgAdv m D) + prfAdv F (multiMsgAdv m' D) +
        2 * ((Nat.choose (q + 1) 2 : ℝ) / 2 ^ n) := by
  have h12 := prfAdv_multiMsgAdv F m D
  have h56 := prfAdv_multiMsgAdv F m' D
  have h23 := distAdv_prfEncReal_random_otp_le m D
  have h45 := distAdv_prfEncReal_random_otp_le m' D
  have h34 := acceptProb_otpEnc m m' D
  simp only [distAdv_def] at h12 h56 h23 h45 ⊢
  rw [h12, h56, abs_sub_comm (acceptProb (prfEncReal F m') D)]
  rw [abs_sub_comm (acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m') D)]
    at h45
  have t1 := abs_sub_le (acceptProb (prfEncReal F m) D)
    (acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) D)
    (acceptProb (prfEncReal F m') D)
  have t2 := abs_sub_le (acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) D)
    (acceptProb (otpEnc m) D) (acceptProb (prfEncReal F m') D)
  have t3 := abs_sub_le (acceptProb (otpEnc m') D)
    (acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m') D)
    (acceptProb (prfEncReal F m') D)
  rw [← h34] at t3 h45
  linarith

end Concrete

end TCSlib.Cryptography
