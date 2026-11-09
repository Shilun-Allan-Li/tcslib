/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Encryption.PublicKey.HybridMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The shared-key hybrid bound

The reduction encrypts every position except the challenge itself under the
public key. It uses advice to choose the position with maximal advantage.

## Main definitions

* `TCSlib.Cryptography.singleDist` and `TCSlib.Cryptography.multiDist` sample one
  encryption and a tuple of encryptions, respectively.
* `TCSlib.Cryptography.hybridAdv` is the planting distinguisher with typed coins.

## Main results

* `TCSlib.Cryptography.distAdv_tuple_le_sum` and `TCSlib.Cryptography.distAdv_tuple_le_mul`
  bound the tuple advantage with a shared public parameter.
* `TCSlib.Cryptography.exists_hybridBound` packages the bound using one non-uniform
  polynomial-time reduction.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (p. 103.)
-/

namespace TCSlib.Cryptography

open Complexity Turing
open PrivateKeyScheme (encodeList)

/-! ## The shared-parameter hybrid bound (concrete) -/

/-- **Planting a single sample into a tuple generated from the adversary's own coins.** If `A` on
`(pk, c pk r)` with coins `(v, r')` is `D` on `(pk, sel pk (update v j r))` with coins `r'`, the
acceptance probability of `A` on the single sample is that of `D` on the full tuple.

**Proof sketch.** Regroup the seeds `(κ × ρ) × ((Fin (q+1) → ρ) × ρ')` as
`ρ × ((Fin (q+1) → ρ) × (κ × ρ'))` and `(κ × (Fin (q+1) → ρ)) × ρ'` as
`(Fin (q+1) → ρ) × (κ × ρ')` (`uprob_comp_equiv`); the event on the left is then
`D (pk, sel pk (update v j r))` and `OneWay.uprob_update` forgets the planted coordinate. -/
private theorem acceptProb_plant {κ π γ ρ ρ' : Type*} [Fintype κ] [Fintype ρ] [Fintype ρ']
    [Nonempty ρ] {q : ℕ} (P : κ → π) (j : Fin (q + 1)) (c : π → ρ → γ)
    (sel : π → (Fin (q + 1) → ρ) → Fin (q + 1) → γ) (D : π × (Fin (q + 1) → γ) → ρ' → Bool)
    (A : π × γ → (Fin (q + 1) → ρ) × ρ' → Bool)
    (hA : ∀ pk r v r', A (pk, c pk r) (v, r') = D (pk, sel pk (Function.update v j r)) r') :
    acceptProb (fun z : κ × ρ => (P z.1, c (P z.1) z.2)) A =
      acceptProb (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, sel (P z.1) z.2)) D := by
  let e₁ : ρ × ((Fin (q + 1) → ρ) × (κ × ρ')) ≃ (κ × ρ) × ((Fin (q + 1) → ρ) × ρ') :=
    { toFun := fun a => ((a.2.2.1, a.1), (a.2.1, a.2.2.2))
      invFun := fun w => (w.1.2, (w.2.1, (w.1.1, w.2.2)))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₂ : (Fin (q + 1) → ρ) × (κ × ρ') ≃ (κ × (Fin (q + 1) → ρ)) × ρ' :=
    { toFun := fun w => ((w.2.1, w.1), w.2.2)
      invFun := fun z => (z.1.2, (z.1.1, z.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simp only [acceptProb_def]
  rw [← uprob_comp_equiv e₁, ← uprob_comp_equiv e₂]
  simp only [e₁, e₂, Equiv.coe_fn_mk, hA]
  exact OneWay.uprob_update (ρ := κ × ρ') (α := ρ) j
    (fun u w => D (P w.1, sel (P w.1) u) w.2 = true)

/-- **The hybrid bound with a shared public parameter**, explicit form (the content of
`TCSlib.Cryptography.distAdv_multi_le_sum`): the advantage of `D` between the `q + 1`
encryptions of `m` and of `m'` under one parameter `P k` is at most the sum over `j` of the
advantages, between the single encryptions of `m_j` and `m'_j`, of the distinguisher that
encrypts `m'_0, …, m'_{j-1}` and `m_{j+1}, …, m_q` itself and plants its sample at position `j`.

**Proof sketch.** Hybrids `H_t := ⟨pk, (E pk m'_i r_i)_{i<t}, (E pk m_i r_i)_{i≥t}⟩`, `t ≤ q + 1`,
on the seeds `κ × (Fin (q+1) → ρ)`, `H_0` and `H_{q+1}` the two sides; `abs_sub_le_sum_hybrids`
over `t ∈ range (q+1)` (`Fin.sum_univ_eq_sum_range`). Each gap `|Pr[D(H_j)] − Pr[D(H_{j+1})]|`
is the advantage of the `j`-th planting distinguisher between `⟨pk, E pk m_j r⟩` and
`⟨pk, E pk m'_j r⟩`: `acceptProb_plant` with the selector of `H_j` (resp. `H_{j+1}`), the
coordinate `v j` being replaced by `r` (`Function.update_apply`, the cases `i < j`, `i = j`,
`i > j` of `Fin.lt_def`). -/
theorem distAdv_tuple_le_sum {κ π μ γ ρ ρ' : Type*} [Fintype κ] [Fintype ρ] [Fintype ρ']
    [Nonempty ρ] {q : ℕ} (P : κ → π) (E : π → μ → ρ → γ) (m m' : Fin (q + 1) → μ)
    (D : π × (Fin (q + 1) → γ) → ρ' → Bool) :
    distAdv (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, fun i => E (P z.1) (m i) (z.2 i)))
      (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, fun i => E (P z.1) (m' i) (z.2 i))) D ≤
    ∑ j : Fin (q + 1), distAdv (fun z : κ × ρ => (P z.1, E (P z.1) (m j) z.2))
      (fun z : κ × ρ => (P z.1, E (P z.1) (m' j) z.2))
      (fun (pc : π × γ) (r : (Fin (q + 1) → ρ) × ρ') => D (pc.1, fun i =>
        if i < j then E pc.1 (m' i) (r.1 i) else if i = j then pc.2 else E pc.1 (m i) (r.1 i)) r.2) := by
  -- the hybrid selector: the first `t` positions carry `m'`, the others `m`
  let sel : ℕ → π → (Fin (q + 1) → ρ) → Fin (q + 1) → γ := fun t pk u i =>
    if (i : ℕ) < t then E pk (m' i) (u i) else E pk (m i) (u i)
  let Pr : ℕ → ℝ := fun t =>
    acceptProb (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, sel t (P z.1) z.2)) D
  have h0 : acceptProb (fun z : κ × (Fin (q + 1) → ρ) =>
      (P z.1, fun i => E (P z.1) (m i) (z.2 i))) D = Pr 0 := by
    simp [Pr, sel]
  have hq : acceptProb (fun z : κ × (Fin (q + 1) → ρ) =>
      (P z.1, fun i => E (P z.1) (m' i) (z.2 i))) D = Pr (q + 1) := by
    simp [Pr, sel, Fin.is_lt]
  have hstep : ∀ j : Fin (q + 1),
      distAdv (fun z : κ × ρ => (P z.1, E (P z.1) (m j) z.2))
        (fun z : κ × ρ => (P z.1, E (P z.1) (m' j) z.2))
        (fun (pc : π × γ) (r : (Fin (q + 1) → ρ) × ρ') => D (pc.1, fun i =>
          if i < j then E pc.1 (m' i) (r.1 i) else if i = j then pc.2 else E pc.1 (m i) (r.1 i))
          r.2) =
      |Pr j - Pr (j + 1)| := by
    intro j
    simp only [distAdv_def]
    rw [acceptProb_plant P j (fun pk r => E pk (m j) r) (sel j) D _,
      acceptProb_plant P j (fun pk r => E pk (m' j) r) (sel (j + 1)) D _]
    · intro pk r v r'
      simp only [sel]
      congr 2
      funext i
      rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
      · have hij : i ≠ j := fun hij => by rw [hij] at h; exact lt_irrefl _ h
        simp [Fin.lt_def, h, hij, Nat.lt_succ_of_lt h]
      · have hij : i = j := Fin.ext h
        subst hij
        simp
      · have hij : i ≠ j := fun hij => by rw [hij] at h; exact lt_irrefl _ h
        have h1 : ¬ (i : ℕ) < j := not_lt.mpr h.le
        have h2 : ¬ (i : ℕ) < (j : ℕ) + 1 := not_lt.mpr h
        simp [Fin.lt_def, h1, h2, hij]
    · intro pk r v r'
      simp only [sel]
      congr 2
      funext i
      rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
      · have hij : i ≠ j := fun hij => by rw [hij] at h; exact lt_irrefl _ h
        simp [Fin.lt_def, h, hij]
      · have hij : i = j := Fin.ext h
        subst hij
        simp
      · have hij : i ≠ j := fun hij => by rw [hij] at h; exact lt_irrefl _ h
        have h1 : ¬ (i : ℕ) < j := not_lt.mpr h.le
        simp [Fin.lt_def, h1, hij]
  have hstart : distAdv
      (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, fun i => E (P z.1) (m i) (z.2 i)))
      (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, fun i => E (P z.1) (m' i) (z.2 i))) D =
      |Pr 0 - Pr (q + 1)| := by
    rw [distAdv_def, h0, hq]
  rw [hstart]
  calc |Pr 0 - Pr (q + 1)|
      ≤ ∑ t ∈ Finset.range (q + 1), |Pr t - Pr (t + 1)| := abs_sub_le_sum_hybrids Pr (q + 1)
    _ = ∑ j : Fin (q + 1), |Pr j - Pr (j + 1)| :=
        (Fin.sum_univ_eq_sum_range (fun t => |Pr t - Pr (t + 1)|) (q + 1)).symm
    _ = _ := Finset.sum_congr rfl fun j _ => (hstep j).symm

/-! ## The samplers of the public-key experiments -/

/-- The single-encryption sampler `{(pk, sk) ← Gen(1^n) : ⟨pk, Enc(1^n, ⟨pk, msg⟩)⟩}` of a key
generator `Gen` and an encryptor `Enc` on the `Lc`-bit message `msg` (the sampler
`PublicKeyScheme.pkEncDist` with its components named). -/
def singleDist (Gen Enc : NUPPT) (n Lc : ℕ) (msg : Fin Lc → Bool) :
    Gen.Coins n × Enc.Coins n → List Bool :=
  fun r => pairEncode (pairFstD (Gen.runAt n [] r.1))
    (Enc.runAt n (pairEncode (pairFstD (Gen.runAt n [] r.1)) (List.ofFn msg)) r.2)

/-- The defining equation of `singleDist`: `singleDist Gen Enc n Lc msg = fun r => pairEncode
(pairFstD (Gen.runAt n [] r.1))
(Enc.runAt n (pairEncode (pairFstD (Gen.runAt n [] r.1)) (List.ofFn msg)) r.2)`. -/
theorem singleDist_def (Gen Enc : NUPPT) (n Lc : ℕ) (msg : Fin Lc → Bool) :
    singleDist Gen Enc n Lc msg =
      (fun r => pairEncode (pairFstD (Gen.runAt n [] r.1))
        (Enc.runAt n (pairEncode (pairFstD (Gen.runAt n [] r.1)) (List.ofFn msg)) r.2) :
        Gen.Coins n × Enc.Coins n → List Bool) := rfl

/-- The multi-encryption sampler `{(pk, sk) ← Gen(1^n) : ⟨pk, ⟨Enc(1^n, ⟨pk, m_0⟩), …⟩⟩}` on `N`
messages of `Lc` bits with independent encryption coins (the sampler
`PublicKeyScheme.pkMultiEncDist`, and the bitwise scheme's ciphertexts read blockwise). -/
def multiDist (Gen Enc : NUPPT) (n N Lc : ℕ) (m : Fin N → Fin Lc → Bool) :
    Gen.Coins n × (Fin N → Enc.Coins n) → List Bool :=
  fun z => pairEncode (pairFstD (Gen.runAt n [] z.1)) (encodeList (List.ofFn fun i =>
    Enc.runAt n (pairEncode (pairFstD (Gen.runAt n [] z.1)) (List.ofFn (m i))) (z.2 i)))

/-- The defining equation of `multiDist`: `⟨pk, ⟨Enc_pk(m_1; r_1), …, Enc_pk(m_N; r_N)⟩⟩`. -/
theorem multiDist_eq (Gen Enc : NUPPT) (n N Lc : ℕ) (m : Fin N → Fin Lc → Bool)
    (z : Gen.Coins n × (Fin N → Enc.Coins n)) :
    multiDist Gen Enc n N Lc m z = pairEncode (pairFstD (Gen.runAt n [] z.1)) (encodeList
      (List.ofFn fun i => Enc.runAt n (pairEncode (pairFstD (Gen.runAt n [] z.1)) (List.ofFn (m i)))
        (z.2 i))) := rfl

/-- **The hybrid bound on string samples**: if every planting distinguisher (on the string
sample `⟨pk, c⟩`, with the tuple encoded by `encodeList`) has advantage at most `t` between the
single encryptions of `m_j` and `m'_j`, then `Dst` has advantage at most `N · t` between the
encoded tuples of the `N` encryptions of `m` and of `m'`.

**Proof sketch.** For `N = 0` the two samplers coincide. For `N = q + 1`, `distAdv_tuple_le_sum`
(the encoding moved into `Dst`, `distAdv_comp`) bounds the advantage by the sum of the `q + 1`
planting advantages, each of which is one of the hypotheses after identifying the
`Fin`-indexed with the `ℕ`-indexed branch conditions (`Fin.lt_def`, `Fin.ext_iff`); the sum of
`q + 1` terms `≤ t` is `≤ (q + 1) t`. -/
theorem distAdv_tuple_le_mul {κ ρ ρ' : Type*} [Fintype κ] [Fintype ρ] [Fintype ρ'] [Nonempty ρ]
    {N Lc : ℕ} (P : κ → List Bool) (E : List Bool → (Fin Lc → Bool) → ρ → List Bool)
    (m m' : Fin N → Fin Lc → Bool) (Dst : List Bool → ρ' → Bool) (t : ℝ)
    (ht : ∀ j : Fin N,
      distAdv (fun z : κ × ρ => pairEncode (P z.1) (E (P z.1) (m j) z.2))
        (fun z : κ × ρ => pairEncode (P z.1) (E (P z.1) (m' j) z.2))
        (fun (s : List Bool) (u : (Fin N → ρ) × ρ') =>
          Dst (pairEncode (pairFstD s) (encodeList (List.ofFn fun i : Fin N =>
            if (i : ℕ) < j then E (pairFstD s) (m' i) (u.1 i) else if (i : ℕ) = j then pairSndD s
            else E (pairFstD s) (m i) (u.1 i)))) u.2) ≤ t) :
    distAdv
      (fun z : κ × (Fin N → ρ) =>
        pairEncode (P z.1) (encodeList (List.ofFn fun i => E (P z.1) (m i) (z.2 i))))
      (fun z : κ × (Fin N → ρ) =>
        pairEncode (P z.1) (encodeList (List.ofFn fun i => E (P z.1) (m' i) (z.2 i)))) Dst ≤
      N * t := by
  cases N with
  | zero =>
    have hm : ∀ z : κ × (Fin 0 → ρ),
        (List.ofFn fun i => E (P z.1) (m i) (z.2 i)) = List.ofFn fun i => E (P z.1) (m' i) (z.2 i) :=
      fun z => congrArg List.ofFn (funext fun i => i.elim0)
    simp only [hm, distAdv_def, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ q =>
    have hterm : ∀ j : Fin (q + 1),
        distAdv (fun z : κ × ρ => (P z.1, E (P z.1) (m j) z.2))
          (fun z : κ × ρ => (P z.1, E (P z.1) (m' j) z.2))
          (fun (pc : List Bool × List Bool) (r : (Fin (q + 1) → ρ) × ρ') =>
            (fun w : List Bool × (Fin (q + 1) → List Bool) =>
              fun r' => Dst (pairEncode w.1 (encodeList (List.ofFn w.2))) r')
            (pc.1, fun i => if i < j then E pc.1 (m' i) (r.1 i) else if i = j then pc.2
              else E pc.1 (m i) (r.1 i)) r.2) ≤ t := by
      intro j
      refine le_of_eq_of_le ?_ (ht j)
      simp only [distAdv_def, acceptProb_def]
      refine congrArg₂ (fun a b : ℝ => |a - b|) (congrArg uprob (funext fun z => ?_))
        (congrArg uprob (funext fun z => ?_)) <;>
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, Fin.lt_def, Fin.ext_iff]
    calc distAdv
          (fun z : κ × (Fin (q + 1) → ρ) =>
            pairEncode (P z.1) (encodeList (List.ofFn fun i => E (P z.1) (m i) (z.2 i))))
          (fun z : κ × (Fin (q + 1) → ρ) =>
            pairEncode (P z.1) (encodeList (List.ofFn fun i => E (P z.1) (m' i) (z.2 i)))) Dst
        = distAdv (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, fun i => E (P z.1) (m i) (z.2 i)))
            (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, fun i => E (P z.1) (m' i) (z.2 i)))
            (fun w r' => Dst (pairEncode w.1 (encodeList (List.ofFn w.2))) r') := rfl
      _ ≤ ∑ j : Fin (q + 1), _ := distAdv_tuple_le_sum P E m m' _
      _ ≤ ∑ _j : Fin (q + 1), t := Finset.sum_le_sum fun j _ => hterm j
      _ = (q + 1 : ℕ) * t := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The `j`-th planting distinguisher of the public-key hybrid argument as a function of the
string sample `⟨pk, c⟩` and typed coins (`N` coin blocks of `Enc`, the coins of `D`): the
behaviour of the hybrid machine `exists_hybridMachine` read through `hybridCoins`. -/
def hybridAdv (Enc D : NUPPT) (n N Lc : ℕ) (m m' : Fin N → Fin Lc → Bool) (j : ℕ) :
    List Bool → (Fin N → Enc.Coins n) × D.Coins n → Bool :=
  fun s u => D.distinguisherL n (pairEncode (pairFstD s) (encodeList (List.ofFn fun i : Fin N =>
    if (i : ℕ) < j then Enc.runAt n (pairEncode (pairFstD s) (List.ofFn (m' i))) (u.1 i)
    else if (i : ℕ) = j then pairSndD s
    else Enc.runAt n (pairEncode (pairFstD s) (List.ofFn (m i))) (u.1 i)))) u.2

/-- **The hybrid bound with a single reduction machine** [PS10, p. 103]: for a key generator
`Gen`, a uniform encryptor `Enc`, a distinguisher `D`, a number of positions `K` and a block
length `L`, and message-vector families `m n, m' n`, there is one non-uniform PPT `B` such that
at every parameter `n`: if `B` distinguishes any two single encryptions of `L(n)`-bit messages
with advantage at most `ε ≥ 0`, then `D` distinguishes the encoded tuples of the `K(n)`
encryptions of `m n` and of `m' n` with advantage at most `K(n) · ε`.

**Proof sketch.** At each `n` with `0 < K(n)` choose the position `j n` maximizing the advantage
of the planting distinguisher `hybridAdv … (j n)` (`Finset.exists_max_image`); the machine `B`
is `exists_hybridMachine` for these positions (hybrid index and messages in the advice). If
`L(n) = 0` the two message vectors coincide and if `K(n) = 0` the two tuples do; otherwise
`distAdv_tuple_le_mul` bounds the advantage by `K(n)` times the maximal planting advantage,
which is the advantage of `B` (`acceptProb_distinguisherL_coins` along `hybridCoins`,
`ofFn_hybridCoins`), hence at most `ε`. -/
theorem exists_hybridBound (Gen Enc D : NUPPT) (hEnc : Enc.Uniform) (K L : PolyExpr)
    (m m' : ∀ n, Fin (K.eval n) → Fin (L.eval n) → Bool) :
    ∃ B : NUPPT, ∀ n (ε : ℝ), 0 ≤ ε →
      (∀ msg msg' : Fin (L.eval n) → Bool,
        distAdv (singleDist Gen Enc n (L.eval n) msg) (singleDist Gen Enc n (L.eval n) msg')
          (B.distinguisherL n) ≤ ε) →
      distAdv (multiDist Gen Enc n (K.eval n) (L.eval n) (m n))
        (multiDist Gen Enc n (K.eval n) (L.eval n) (m' n)) (D.distinguisherL n) ≤ K.eval n * ε := by
  classical
  -- the advantage of the `j`-th planting distinguisher at parameter `n`
  let term : ∀ n, Fin (K.eval n) → ℝ := fun n j =>
    distAdv (singleDist Gen Enc n (L.eval n) (m n j)) (singleDist Gen Enc n (L.eval n) (m' n j))
      (hybridAdv Enc D n (K.eval n) (L.eval n) (m n) (m' n) j)
  -- the maximizing position at each parameter
  have hmax : ∀ n, ∃ j : ℕ, 0 < K.eval n → ∃ hj : j < K.eval n,
      ∀ jf : Fin (K.eval n), term n jf ≤ term n ⟨j, hj⟩ := by
    intro n
    by_cases hK : 0 < K.eval n
    · haveI : Nonempty (Fin (K.eval n)) := ⟨⟨0, hK⟩⟩
      obtain ⟨jf, -, hjf⟩ := Finset.exists_max_image Finset.univ (term n) Finset.univ_nonempty
      exact ⟨jf, fun _ => ⟨jf.isLt, fun j' => hjf j' (Finset.mem_univ _)⟩⟩
    · exact ⟨0, fun h => absurd h hK⟩
  choose jN hjN using hmax
  obtain ⟨B, hBc, hB⟩ := exists_hybridMachine Enc D hEnc K L jN m m'
  refine ⟨B, fun n ε hε hsingle => ?_⟩
  rcases Nat.eq_zero_or_pos (L.eval n) with hL | hL
  · -- no message bits: the two vectors coincide
    have hmm : m n = m' n := funext fun i => funext fun b => absurd b.isLt (by omega)
    rw [hmm, distAdv_def, sub_self, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hε
  rcases Nat.eq_zero_or_pos (K.eval n) with hK | hK
  · -- no positions: the two tuples coincide
    have hmm : ∀ z : Gen.Coins n × (Fin (K.eval n) → Enc.Coins n),
        multiDist Gen Enc n (K.eval n) (L.eval n) (m n) z =
          multiDist Gen Enc n (K.eval n) (L.eval n) (m' n) z := by
      intro z
      simp only [multiDist]
      congr 3
      exact funext fun i => absurd i.isLt (by omega)
    simp only [distAdv_def, acceptProb_def, hmm, sub_self, abs_zero, hK, Nat.cast_zero, zero_mul,
        le_refl]
  obtain ⟨hj, hjmax⟩ := hjN n hK
  -- the maximal planting advantage is the advantage of the machine `B`
  have hmach : ∀ msg : Fin (L.eval n) → Bool,
      acceptProb (singleDist Gen Enc n (L.eval n) msg)
          (hybridAdv Enc D n (K.eval n) (L.eval n) (m n) (m' n) (jN n)) =
        acceptProb (singleDist Gen Enc n (L.eval n) msg) (B.distinguisherL n) := by
    intro msg
    refine (acceptProb_distinguisherL_coins B n _ (hybridCoins B Enc D K n hBc) _ ?_).symm
    rintro ⟨r, s⟩ ⟨v, ρ⟩
    simp only [singleDist, hybridAdv, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, ofFn_hybridCoins,
      hB n hj hL, pairFstD_pairEncode, pairSndD_pairEncode]
  have hbound : term n ⟨jN n, hj⟩ ≤ ε := by
    simp only [term, distAdv_def, hmach]
    exact hsingle _ _
  calc distAdv (multiDist Gen Enc n (K.eval n) (L.eval n) (m n))
        (multiDist Gen Enc n (K.eval n) (L.eval n) (m' n)) (D.distinguisherL n)
      ≤ K.eval n * term n ⟨jN n, hj⟩ :=
        distAdv_tuple_le_mul (fun r => pairFstD (Gen.runAt n [] r))
          (fun pk msg r => Enc.runAt n (pairEncode pk (List.ofFn msg)) r) (m n) (m' n)
          (D.distinguisherL n) _ (fun j => hjmax j)
    _ ≤ K.eval n * ε := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)

end TCSlib.Cryptography
