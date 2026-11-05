/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Bridge
import TCSlib.Complexity.SpaceComplexity.Machines.ARMWidth

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Midpoint reachability over configuration codes

The predicate evaluated by Savitch's algorithm [AB09, §4.2.1, proof of Theorem 4.14]:
`Complexity.LogProg.SavitchARM.Reach K R i u v` holds when `v` is reachable from `u` in at
most `2 ^ i` steps of the relation `R`, witnessed by midpoints below `K` —
`Reach K R 0 u v` is `u = v ∨ R u v`, and `Reach K R (i + 1) u v` asks for some `m < K`
with `Reach K R i u m` and `Reach K R i m v`.

Over the code languages of a nondeterministic space-bounded decider `N`
(`TCSlib.Complexity.SpaceComplexity.Codec`), membership is midpoint reachability from an
initial code to an accepting code (`Complexity.LogProg.SavitchARM.mem_iff_reach`), once the
code width `w` is large enough that the codes lie below `2 ^ w` and the configuration count
is at most `2 ^ w`: chains of length at most `2 ^ w` are cut at midpoints
(`reach_of_chain`), and conversely every midpoint witness unfolds into a path of steps
(`reflTransGen_of_reach`), whose codes are realized by a branch of `N`
(`Complexity.Codec.mem_of_codePath`).

## Main definitions

* `Complexity.LogProg.SavitchARM.Reach` — midpoint reachability (over the code-level step
  relation `Complexity.Codec.StepRel` of a decider).

## Main results

* `Complexity.LogProg.SavitchARM.reach_of_chain`, `reflTransGen_of_reach` — the two
  directions of midpoint reachability.
* `Complexity.LogProg.SavitchARM.configBound_le` — the configuration count at radius
  `(n + 2) ^ E` is below `2 ^ ((n + 2) ^ (2 E))`.
* `Complexity.LogProg.SavitchARM.mem_iff_reach` — membership as midpoint reachability.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Claim 4.4; §4.2.1, Theorem 4.14.)
-/

namespace Complexity.LogProg

namespace SavitchARM

open Turing Codec

/-- **Midpoint reachability**: `Reach K R i u v` holds when `v` is reachable from `u` in at
most `2 ^ i` steps of `R`, with every midpoint of the recursion below `K`. [AB09, §4.2.1,
the predicate `REACH(C, C', i)` of the proof of Theorem 4.14] -/
def Reach (K : ℕ) (R : ℕ → ℕ → Prop) : ℕ → ℕ → ℕ → Prop
  | 0, u, v => u = v ∨ R u v
  | i + 1, u, v => ∃ m < K, Reach K R i u m ∧ Reach K R i m v

/-- **Chains are cut at midpoints**: a chain `c 0, …, c T` of `R`-steps with every member
below `K` gives `Reach K R i (c j) (c (j + t))` for every segment of length `t ≤ 2 ^ i`.

**Proof sketch.** Induction on `i`. A segment of length at most one is an equality or a
step. A segment of length `t ≤ 2 ^ (i + 1)` splits at `t₁ = min t (2 ^ i)` into two
segments of length at most `2 ^ i`, the split point `c (j + t₁)` serving as midpoint. -/
theorem reach_of_chain (K : ℕ) (R : ℕ → ℕ → Prop) (c : ℕ → ℕ) (T : ℕ)
    (hR : ∀ j < T, R (c j) (c (j + 1))) (hK : ∀ j ≤ T, c j < K) :
    ∀ i j t, j + t ≤ T → t ≤ 2 ^ i → Reach K R i (c j) (c (j + t)) := by
  intro i
  induction i with
  | zero =>
    intro j t hjt ht
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact Or.inl rfl
    · obtain rfl : t = 1 := by simp at ht; omega
      exact Or.inr (hR j (by omega))
  | succ i ih =>
    intro j t hjt ht
    set t₁ := min t (2 ^ i) with ht₁
    have h1 : t₁ ≤ 2 ^ i := min_le_right _ _
    have h2 : t - t₁ ≤ 2 ^ i := by rw [pow_succ] at ht; omega
    refine ⟨c (j + t₁), hK _ (by omega), ih j t₁ (by omega) h1, ?_⟩
    have := ih (j + t₁) (t - t₁) (by omega) h2
    rwa [show j + t₁ + (t - t₁) = j + t by omega] at this

/-- **Midpoint witnesses unfold into paths**: `Reach K R i u v` gives an `R`-path from `u`
to `v`.

**Proof sketch.** Induction on `i`: an equality or a step is a path, and two paths through
a midpoint concatenate. -/
theorem reflTransGen_of_reach (K : ℕ) (R : ℕ → ℕ → Prop) :
    ∀ i u v, Reach K R i u v → Relation.ReflTransGen R u v := by
  intro i
  induction i with
  | zero =>
    rintro u v (rfl | h)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single h
  | succ i ih =>
    rintro u v ⟨m, -, h1, h2⟩
    exact (ih u m h1).trans (ih m v h2)

/-! ## The size bounds -/

/-- **The configuration count is doubly exponentially bounded**: at radius `(n + 2) ^ E`,
with `|Q| + 2 + 9k ≤ E`, the vertex count `configBound n ((n + 2) ^ E)` is at most
`2 ^ ((n + 2) ^ (2 E))`.

**Proof sketch.** Bound each factor of
`3 (|Q| + 1)(n + 2) 3 ^ (k (2s + 1)) (2s + 1) ^ k` by a power of two: the exponents add up
to at most `|Q| + n + 3 + 3k (2s + 1) ≤ (|Q| + 2 + 9k) s ≤ 2 ^ E s ≤ (n + 2) ^ E s`. -/
theorem configBound_le (N : FinNDTM Bool) (n E : ℕ)
    (hE : Fintype.card N.State + 2 + 9 * N.k ≤ E) :
    N.configBound n ((n + 2) ^ E) ≤ 2 ^ ((n + 2) ^ (2 * E)) := by
  set s := (n + 2) ^ E with hs
  set Q := Fintype.card N.State
  set k := N.k
  have hs1 : n + 2 ≤ s := by
    have : 1 ≤ E := by omega
    calc n + 2 = (n + 2) ^ 1 := (pow_one _).symm
      _ ≤ s := Nat.pow_le_pow_right (by omega) this
  have f1 : 3 ≤ 2 ^ 2 := by decide
  have f2 : Q + 1 ≤ 2 ^ Q := Nat.lt_two_pow_self
  have f3 : n + 2 ≤ 2 ^ (n + 1) := Nat.lt_two_pow_self
  have f4 : 3 ^ (k * (2 * s + 1)) ≤ 2 ^ (2 * (k * (2 * s + 1))) := by
    rw [pow_mul 2 2]; exact Nat.pow_le_pow_left f1 _
  have f5 : (2 * s + 1) ^ k ≤ 2 ^ (k * (2 * s + 1)) := by
    rw [pow_mul']; exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
  have hprod : N.configBound n s ≤
      2 ^ (2 + Q + (n + 1) + 2 * (k * (2 * s + 1)) + k * (2 * s + 1)) := by
    unfold FinNDTM.configBound
    rw [pow_add, pow_add, pow_add, pow_add]
    have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul f2 f3) f4) f5) f1
    calc 3 * ((Q + 1) * (n + 2) * 3 ^ (k * (2 * s + 1)) * (2 * s + 1) ^ k)
        = (Q + 1) * (n + 2) * 3 ^ (k * (2 * s + 1)) * (2 * s + 1) ^ k * 3 := by ring
      _ ≤ 2 ^ Q * 2 ^ (n + 1) * 2 ^ (2 * (k * (2 * s + 1))) * 2 ^ (k * (2 * s + 1)) * 2 ^ 2 :=
        this
      _ = _ := by ring
  refine hprod.trans (Nat.pow_le_pow_right (by norm_num) ?_)
  -- the exponent: `Q + n + 3 + 3k (2s + 1) ≤ (Q + 2 + 9k) s ≤ 2 ^ E s ≤ (n + 2) ^ E s`
  have hE2 : Q + 2 + 9 * k ≤ (n + 2) ^ E :=
    hE.trans ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by omega) _))
  have e1 : (n + 2) ^ (2 * E) = s * s := by rw [hs, ← pow_add]; ring_nf
  rw [e1]
  have g1 : (Q + 2 + 9 * k) * s ≤ s * s := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hE2
  have g2 : Q ≤ Q * s := Nat.le_mul_of_pos_right _ (by omega)
  have g3 : k ≤ k * s := Nat.le_mul_of_pos_right _ (by omega)
  have e2 : (Q + 2 + 9 * k) * s = Q * s + 2 * s + 9 * (k * s) := by ring
  have e3 : 2 + Q + (n + 1) + 2 * (k * (2 * s + 1)) + k * (2 * s + 1) =
      Q + n + 3 + 6 * (k * s) + 3 * k := by ring
  omega

/-- **The code width bound**: with `2 codeK N ≤ E`, the codes at radius `(n + 2) ^ E` on
inputs of length `n` have width at most `(n + 2) ^ (2 E)`.

**Proof sketch.** `logSpace n + 1 ≤ n + 2 ≤ (n + 2) ^ E`, so the width
`codeK N ((n + 2) ^ E + logSpace n + 1)` is at most `2 codeK N (n + 2) ^ E`, and
`2 codeK N ≤ E < 2 ^ E ≤ (n + 2) ^ E`. -/
theorem codeWidth_le (N : FinNDTM Bool) (n E : ℕ) (hE : 2 * codeK N ≤ E) :
    codeK N * ((n + 2) ^ E + logSpace n + 1) ≤ (n + 2) ^ (2 * E) := by
  set s := (n + 2) ^ E with hs
  have hlog := logSpace_le_succ n
  have hs1 : n + 2 ≤ s := by
    rcases Nat.eq_zero_or_pos E with h | h
    · have : codeK N = 0 := by omega
      simp [codeK, W] at this
    · calc n + 2 = (n + 2) ^ 1 := (pow_one _).symm
        _ ≤ s := Nat.pow_le_pow_right (by omega) h
  have hE2 : 2 * codeK N ≤ s :=
    hE.trans ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by omega) _))
  have e1 : (n + 2) ^ (2 * E) = s * s := by rw [hs, ← pow_add]; ring_nf
  rw [e1]
  calc codeK N * (s + logSpace n + 1) ≤ codeK N * (2 * s) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * codeK N * s := by ring
    _ ≤ s * s := Nat.mul_le_mul_right _ hE2

/-- **The radius bound**: with `k + c + 1 ≤ E`, `c (n ^ k + 1) ≤ (n + 2) ^ E`.

**Proof sketch.** `n ^ k + 1 ≤ 2 (n + 2) ^ k` and `c < 2 ^ c ≤ (n + 2) ^ c`, so
`c (n ^ k + 1) ≤ 2 (n + 2) ^ (k + c) ≤ (n + 2) ^ (k + c + 1)`. -/
theorem radius_le (n k c E : ℕ) (hE : k + c + 1 ≤ E) :
    c * (n ^ k + 1) ≤ (n + 2) ^ E := by
  have h1 : n ^ k + 1 ≤ 2 * (n + 2) ^ k := by
    have : n ^ k ≤ (n + 2) ^ k := Nat.pow_le_pow_left (by omega) _
    have : 1 ≤ (n + 2) ^ k := Nat.one_le_pow _ _ (by omega)
    omega
  have h2 : 2 * c ≤ (n + 2) ^ c * 2 := by
    have : c < 2 ^ c := Nat.lt_two_pow_self
    have : 2 ^ c ≤ (n + 2) ^ c := Nat.pow_le_pow_left (by omega) _
    omega
  calc c * (n ^ k + 1) ≤ c * (2 * (n + 2) ^ k) := Nat.mul_le_mul_left _ h1
    _ = 2 * c * (n + 2) ^ k := by ring
    _ ≤ (n + 2) ^ c * 2 * (n + 2) ^ k := Nat.mul_le_mul_right _ h2
    _ = 2 * (n + 2) ^ (k + c) := by rw [pow_add]; ring
    _ ≤ (n + 2) ^ (k + c + 1) := by
        rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    _ ≤ (n + 2) ^ E := Nat.pow_le_pow_right (by omega) hE

/-- **Membership as midpoint reachability** [AB09, §4.2.1, proof of Theorem 4.14]: let `N`
decide `L` in space `sp`, and let the radius `s ≥ sp |x|` and the width `w` be such that the
codes have width at most `w` and the configuration count is at most `2 ^ w`. Then `x ∈ L` iff
some initial code `u < 2 ^ w` and some accepting code `v < 2 ^ w` have
`Reach (2 ^ w) (StepRel N x s) w u v`.

**Proof sketch.** (⇒) `Complexity.Codec.mem_iff_codeChain` gives a chain of codes below
`2 ^ w` of length at most the configuration count, hence at most `2 ^ w`; cut it at midpoints
(`reach_of_chain`). (⇐) Unfold the midpoint witness into a path (`reflTransGen_of_reach`) and
realize it by a branch (`Complexity.Codec.mem_of_codePath`). -/
theorem mem_iff_reach {N : FinNDTM Bool} {L : Language Bool} {sp : ℕ → ℕ}
    (h : N.DecidesInSpace L sp) (x : List Bool) (s w : ℕ) (hs : sp x.length ≤ s)
    (hw : codeK N * (s + logSpace x.length + 1) ≤ w)
    (hcb : N.configBound x.length s ≤ 2 ^ w) :
    x ∈ L ↔ ∃ u < 2 ^ w, pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ initLang N ∧
      ∃ v < 2 ^ w, pairEncode x (pairEncode (Nat.bits v) (Nat.bits s)) ∈ acceptLang N ∧
        Reach (2 ^ w) (StepRel N x s) w u v := by
  constructor
  · intro hx
    obtain ⟨t, c, ht, hinit, hstep, hacc, hlt⟩ := (mem_iff_codeChain h x s hs).mp hx
    have hK : ∀ j ≤ t, c j < 2 ^ w := fun j hj =>
      (hlt j hj).trans_le (Nat.pow_le_pow_right (by norm_num) hw)
    have hr := reach_of_chain (2 ^ w) (StepRel N x s) c t hstep hK w 0 t (by omega)
      (ht.trans hcb)
    rw [zero_add] at hr
    exact ⟨c 0, hK 0 (Nat.zero_le _), hinit, c t, hK t le_rfl, hacc, hr⟩
  · rintro ⟨u, -, hinit, v, -, hacc, hr⟩
    exact mem_of_codePath h x s u v hinit (reflTransGen_of_reach _ _ w u v hr) hacc

end SavitchARM

end Complexity.LogProg
