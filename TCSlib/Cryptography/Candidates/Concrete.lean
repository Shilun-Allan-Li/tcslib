/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.OneWayFunctions.Amplification
import TCSlib.Cryptography.NumberTheory.Chebyshev
import TCSlib.Cryptography.NumberTheory.Units
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Candidates.Arithmetic
import Mathlib.Logic.Equiv.Prod

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Concrete lemmas for the factoring-based candidates

The concrete-layer content of the reductions of [PS10, §2.3–§2.4, §2.7] (Theorems 33.5,
36.3, 51.1), stated as exact inequalities at one security parameter in the style of
[Gar26] and consumed by `TCSlib.Cryptography.Candidates.Factoring`:

* *conditioning* (lemma C1 of the chapter 2 inventory): the probability of an event on the
  uniform subtype `{a // E a}` is `Pr[E ∧ S] / Pr[E]`, and is at least
  `1 - (1 - Pr[S]) / δ` when `Pr[E] ≥ δ` — the step of [PS10, Theorem 33.5] turning an
  inverter of `f_mult` on uniform pairs into a factorer on uniform *prime* pairs;
* the *diagonal*: a uniform pair of elements of a finite type coincides with probability
  `1 / |γ|` (the switch from `Π_n × Π_n` to pairs of distinct primes);
* *random-position planting with a good set* (lemma C3): the one-call reduction of
  [PS10, Algorithm 37.4] (plant the challenge at a uniform position of a fresh tuple,
  `OneWay.yaoTry`) inverts `f` on a uniform *good* input with probability at least
  `(μ - (1 - Pr[G])^m) / m`, `μ` the success of the inverter of the direct product
  `prodFun f m` — the mirror of `OneWay.invProb_prodFun_le` [Gar26, Theorem 2.1] with the
  bad set replaced by the complement of the good set;
* the *tail bound* `(1 - 1/a)^{a k} ≤ e^{-k}` (lemma C8) and its instance
  `(1 - 1/(4n²))^{4n³} ≤ e^{-n}` [PS10, Claim 36.2], with `e^{-n} ≤ 2^{-n}`;
* the *prime-pair density* on `n`-bit strings and the identification of the uniform subtype
  of prime pairs with `Π_n × Π_n` (`primesPairEquiv`);
* the type `DistinctPrimes n` of pairs of distinct primes of `Π_n` (the restriction `p ≠ q`
  of the decision log "Rabin/RSA scope") with its string encoding, its `NeZero`/`Fact`
  instances and `Φ(pq) = (p−1)(q−1)` (moved here from `RSA.lean`, run-3 audit P7-6);
* *block rejection sampling* on coin lists (`rejectBlocksL`, run-3 audit P7-6): the one
  sampler behind the honest samplers of `Z_N^*`, `Z*_{Φ(N)}` and the restricted prime classes
  of [PS10, §2.9–§2.12], with its closeness lemma `statClose_rejectBlocksL` (lemma C4 on
  coin lists).

## Main definitions

* `TCSlib.Cryptography.Candidates.primesPairEquiv` — prime pairs of `n`-bit strings as
  `Π_n × Π_n`.
* `TCSlib.Cryptography.Candidates.DistinctPrimes` — pairs of distinct primes of `Π_n` (the
  index distribution of the factoring assumption and of the RSA/Rabin moduli), with
  `DistinctPrimes.default`, `encodeDistinctPrimes`, `decodeDistinctPrimes`.
* `TCSlib.Cryptography.Candidates.rejectBlocksL` — block rejection sampling on a coin list.

## Main results

* `TCSlib.Cryptography.Candidates.uprob_and_eq_mul_subtype`,
  `TCSlib.Cryptography.Candidates.one_sub_div_le_uprob_subtype` (C1),
  `TCSlib.Cryptography.Candidates.uprob_le_uprob_subtype_add`,
  `TCSlib.Cryptography.Candidates.uprob_subtype_prod_eq` — conditioning on an event.
* `TCSlib.Cryptography.Candidates.uprob_diag` — the diagonal of a uniform pair.
* `TCSlib.Cryptography.Candidates.invProb_prodFun_le_plant` (C3) — random-position
  planting with a good set [PS10, Algorithm 37.4, Theorem 36.3].
* `TCSlib.Cryptography.Candidates.one_sub_one_div_pow_le_exp_neg` (C8),
  `TCSlib.Cryptography.Candidates.claim_36_2` [PS10, Claim 36.2],
  `TCSlib.Cryptography.Candidates.exp_neg_le_half_pow`.
* `TCSlib.Cryptography.Candidates.one_div_le_uprob_prime_pair_bits`,
  `TCSlib.Cryptography.Candidates.one_div_card_primes_le` — density facts in the forms
  the reductions use.
* `TCSlib.Cryptography.Candidates.decodeDistinctPrimes_encode`,
  `TCSlib.Cryptography.Candidates.DistinctPrimes.isEmpty_of_lt` — the encoding of distinct
  prime pairs is lossless; `Π_n` has no two distinct primes for `n < 2`.
* `TCSlib.Cryptography.Candidates.DistinctPrimes.totient_mul`,
  `TCSlib.Cryptography.Candidates.DistinctPrimes.one_lt_totient` — `Φ(pq) = (p−1)(q−1) ≥ 2`.
* `TCSlib.Cryptography.Candidates.rejectBlocksL_spec`,
  `TCSlib.Cryptography.Candidates.statClose_rejectBlocksL` — accepted values satisfy the
  test; the total sampler is within `(1 − Pr[E])^T` of uniform on `E`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.3.1–§2.3.2, Theorem 33.5, Algorithm 33.6; §2.4.2, Claim 36.2, Theorem 36.3,
  Algorithm 37.4; §2.7, Theorem 51.1.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (Theorem 2.1 and Figure 2.2: planting at a uniform
  position).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing Finset TCSlib.Cryptography.OneWay NumberTheory

/-! ## Conditioning on an event (lemma C1) -/

section Conditioning

variable {α ρ : Type*} [Fintype α] [Fintype ρ]

/-- **Conditioning, multiplicative form**: `Pr[E ∧ S] = Pr[E] · Pr[S | E]`, where `Pr[S | E]`
is the probability of `S` under the uniform distribution on the subtype `{a // E a}`
(lemma C1 of the chapter 2 inventory, [PS10, proof of Theorem 33.5]: "`A'` feeds `A` a
uniformly distributed input … and replaces `xy` with `z` if both are prime"). -/
theorem uprob_and_eq_mul_subtype (E S : α → Prop) [DecidablePred E] :
    uprob (fun a => E a ∧ S a) = uprob E * uprob (fun z : {a // E a} => S z.1) := by
  unfold uprob
  rw [← Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter E S)]
  rcases (Fintype.card {a // E a}).eq_zero_or_pos with h0 | hpos
  · haveI : IsEmpty {a // E a} := Fintype.card_eq_zero_iff.mp h0
    have h1 : Nat.card {z : {a // E a} // S z.1} = 0 := Nat.card_of_isEmpty
    have h2 : Nat.card {a // E a} = 0 := Nat.card_of_isEmpty
    rw [h1, h2]
    simp
  · rw [Nat.card_eq_fintype_card (α := {a // E a})]
    have hc : (Fintype.card {a // E a} : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp

/-- **Conditioning, lower bound** (lemma C1, [PS10, proof of Theorem 33.5, the union
bound]): if `Pr[E] ≥ δ > 0` then `Pr[S | E] ≥ 1 - (1 - Pr[S]) / δ`. With `Pr[E] ≥ 1/(4n²)`
and `1 - Pr[S] ≤ 1/(8(n+1)²)` this gives `Pr[S | E] ≥ 1/2`.

**Proof sketch.** `Pr[S] ≤ Pr[E ∧ S] + Pr[¬E] = Pr[E]·Pr[S | E] + 1 - Pr[E]`, so
`Pr[E]·(1 - Pr[S | E]) ≤ 1 - Pr[S]`; divide by `Pr[E] ≥ δ`. -/
theorem one_sub_div_le_uprob_subtype (E S : α → Prop) [DecidablePred E] {δ : ℝ} (hδ : 0 < δ)
    (hE : δ ≤ uprob E) : 1 - (1 - uprob S) / δ ≤ uprob (fun z : {a // E a} => S z.1) := by
  haveI : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h0 : uprob E = 0 := by
      unfold uprob
      simp
    linarith
  have hES := uprob_and_eq_mul_subtype E S
  have hsplit : uprob S ≤ uprob (fun a => E a ∧ S a) + uprob (fun a => ¬ E a) := by
    refine (uprob_mono ?_).trans (uprob_or_le _ _)
    intro a ha
    by_cases hEa : E a
    · exact Or.inl ⟨hEa, ha⟩
    · exact Or.inr hEa
  rw [uprob_not, hES] at hsplit
  have hEpos : 0 < uprob E := lt_of_lt_of_le hδ hE
  have h1 : 1 - uprob (fun z : {a // E a} => S z.1) ≤ (1 - uprob S) / uprob E := by
    rw [le_div_iff₀ hEpos]
    nlinarith
  have h2 : (1 - uprob S) / uprob E ≤ (1 - uprob S) / δ :=
    div_le_div_of_nonneg_left (by linarith [uprob_le_one S]) hδ hE
  linarith

/-- **Dropping a conditioning**: `Pr[S] ≤ Pr[S | E] + Pr[¬E]` (the switch from the uniform
pair of primes `Π_n × Π_n` to the uniform pair of *distinct* primes, whose complement — the
diagonal — has probability `1/|Π_n|`). -/
theorem uprob_le_uprob_subtype_add (E S : α → Prop) [DecidablePred E] :
    uprob S ≤ uprob (fun z : {a // E a} => S z.1) + uprob (fun a => ¬ E a) := by
  have hES := uprob_and_eq_mul_subtype E S
  have hsplit : uprob S ≤ uprob (fun a => E a ∧ S a) + uprob (fun a => ¬ E a) := by
    refine (uprob_mono ?_).trans (uprob_or_le _ _)
    intro a ha
    by_cases hEa : E a
    · exact Or.inl ⟨hEa, ha⟩
    · exact Or.inr hEa
  have h1 : uprob (fun a => E a ∧ S a) ≤ uprob (fun z : {a // E a} => S z.1) := by
    rw [hES]
    exact mul_le_of_le_one_left (uprob_nonneg _) (uprob_le_one _)
  linarith

/-- Conditioning on the first coordinate of a product: the uniform subtype `{a // E a}` with
independent auxiliary coins `ρ` is the uniform subtype of pairs whose first coordinate
satisfies `E` (relabelling by `Equiv.prodSubtypeFstEquivSubtypeProd`). -/
theorem uprob_subtype_prod_eq (E : α → Prop) [DecidablePred E] (S : α × ρ → Prop) :
    uprob (fun z : {a // E a} × ρ => S (z.1.1, z.2)) =
      uprob (fun z : {w : α × ρ // E w.1} => S z.1) :=
  uprob_comp_equiv (Equiv.prodSubtypeFstEquivSubtypeProd (p := E)).symm fun z => S z.1

/-- **The diagonal**: a uniform pair of elements of a nonempty finite type consists of equal
elements with probability `1 / |γ|`. -/
theorem uprob_diag {γ : Type*} [Fintype γ] [DecidableEq γ] [Nonempty γ] :
    uprob (fun z : γ × γ => z.2 = z.1) = 1 / Fintype.card γ := by
  rw [uprob_prod]
  simp only [uprob_eq_one_div_card]
  exact uexp_const _

end Conditioning

/-! ## Random-position planting with a good set (lemma C3) -/

section Planting

variable {α β ρ : Type*} [Fintype α] [Fintype ρ] {m : ℕ}

/-- **Random-position planting with a good set** (lemma C3 of the chapter 2 inventory; the
concrete content of [PS10, Theorem 36.3] with the one-call reduction of
[PS10, Algorithm 37.4] planting the challenge at a *uniform* position): if `B` inverts the
direct product `prodFun f m` with probability `μ`, then either every coordinate of the
uniform tuple is outside the good set `G` (probability `(1 - Pr[G])^m`) or the one-call
reduction `yaoTry f B` (plant `f x` at the uniform position `i` of a fresh tuple, call `B`,
return the `i`-th answer) inverts `f(x)` for a uniform `x` lying in `G`:
`μ ≤ (1 - Pr[G])^m + m · Pr_{x, i, xs, r}[x ∈ G ∧ f(yaoTry f B (f x) (i, xs, r)) = f x]`.
Mirror of `OneWay.invProb_prodFun_le` [Gar26, Theorem 2.1] with the bad set replaced by
`¬G`.

**Deviation:** [PS10, Algorithm 37.4] plants at the first prime pair and tests primality;
planting at a uniform position needs no primality test (the text's exercise, p. 37).

**Proof sketch.** Success of `B` on `(xs, r)` means that every `xs i` is outside `G` or that
some position `i` has `xs i ∈ G` and the `i`-th answer inverts `f (xs i)`
(`uprob_mono`, `uprob_or_le`, `uprob_exists_le`). The first event has probability
`(1 - Pr[G])^m` (`uprob_fst`, `OneWay.uprob_pi_forall`, `uprob_not`). For fixed `i`, planting
a fresh uniform `x` at position `i` leaves the tuple uniform (`OneWay.uprob_update`,
`OneWay.prodFun_update`), which rewrites the `i`-th event as the planted experiment; summing
over `i` makes the position uniform (`OneWay.sum_uprob_eq_card_mul`), and a relabelling of
the coin space finishes. -/
theorem invProb_prodFun_le_plant [Nonempty α] [Nonempty ρ] (f : α → β)
    (B : (Fin m → β) → ρ → (Fin m → α)) (G : α → Prop) :
    invProb (prodFun f m) B ≤ (1 - uprob G) ^ m +
      m * uprob (fun z : α × (Fin m × ((Fin m → α) × ρ)) =>
        G z.1 ∧ f (yaoTry f B (f z.1) z.2) = f z.1) := by
  classical
  unfold invProb
  calc uprob (fun z : (Fin m → α) × ρ =>
        prodFun f m (B (prodFun f m z.1) z.2) = prodFun f m z.1)
      ≤ uprob (fun z : (Fin m → α) × ρ => (∀ i, ¬ G (z.1 i)) ∨
          ∃ i ∈ (univ : Finset (Fin m)),
            G (z.1 i) ∧ f (B (prodFun f m z.1) z.2 i) = f (z.1 i)) := by
        apply uprob_mono
        rintro ⟨xs, r⟩ h
        by_cases hall : ∀ i, ¬ G (xs i)
        · exact Or.inl hall
        · push_neg at hall
          obtain ⟨i, hi⟩ := hall
          exact Or.inr ⟨i, mem_univ _, hi, congrFun h i⟩
    _ ≤ uprob (fun z : (Fin m → α) × ρ => ∀ i, ¬ G (z.1 i)) +
          ∑ i, uprob (fun z : (Fin m → α) × ρ =>
            G (z.1 i) ∧ f (B (prodFun f m z.1) z.2 i) = f (z.1 i)) :=
        (uprob_or_le _ _).trans (add_le_add_left (uprob_exists_le _ _) _)
    _ ≤ _ := by
        apply add_le_add
        · rw [uprob_fst (fun xs : Fin m → α => ∀ i, ¬ G (xs i)),
            uprob_pi_forall (ι := Fin m) (fun x => ¬ G x), uprob_not, Fintype.card_fin]
        · have hplant : ∀ i, uprob (fun z : (Fin m → α) × ρ =>
              G (z.1 i) ∧ f (B (prodFun f m z.1) z.2 i) = f (z.1 i)) =
              uprob (fun z : α × ((Fin m → α) × ρ) =>
                G z.1 ∧ f (yaoTry f B (f z.1) (i, z.2)) = f z.1) := by
            intro i
            rw [← uprob_update i (fun xs r =>
              G (xs i) ∧ f (B (prodFun f m xs) r i) = f (xs i))]
            apply uprob_congr
            rintro ⟨x, xs, r⟩
            simp [yaoTry, prodFun_update]
          simp only [hplant]
          rw [sum_uprob_eq_card_mul, Fintype.card_fin]
          let e : α × (Fin m × ((Fin m → α) × ρ)) ≃ Fin m × (α × ((Fin m → α) × ρ)) :=
            { toFun := fun z => (z.2.1, (z.1, z.2.2))
              invFun := fun z => (z.2.1, (z.1, z.2.2))
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
          rw [← uprob_comp_equiv e]
          exact le_rfl

end Planting

/-! ## Tail bounds (lemma C8, Claim 36.2) -/

/-- **Tail bound** (lemma C8 of the chapter 2 inventory): `(1 - 1/a)^{a·k} ≤ e^{-k}` for
`a ≥ 1` (the inequality `1 - t ≤ e^{-t}` raised to the power `a·k`,
`Real.one_sub_div_pow_le_exp_neg`). -/
theorem one_sub_one_div_pow_le_exp_neg (a k : ℕ) (ha : 0 < a) :
    (1 - 1 / (a : ℝ)) ^ (a * k) ≤ Real.exp (-(k : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have h := Real.one_sub_div_pow_le_exp_neg (n := a * k) (t := (k : ℝ))
    (by push_cast; nlinarith [(by exact_mod_cast ha : (1 : ℝ) ≤ a), (by exact_mod_cast hk : (0 : ℝ) < k)])
  have heq : (1 - (k : ℝ) / ((a * k : ℕ) : ℝ)) = 1 - 1 / (a : ℝ) := by
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    push_cast
    field_simp
  rw [heq] at h
  exact h

/-- **Claim 36.2** [PS10, (36.2)]: `(1 - 1/(4n²))^{4n³} = ((1 - 1/(4n²))^{4n²})^n ≤ e^{-n}`:
with `4n³` pairs of random `n`-bit numbers, the probability that none of them is a pair of
primes is at most `e^{-n}` (given the density `1/(4n²)` of prime pairs). -/
theorem claim_36_2 (n : ℕ) (hn : 0 < n) :
    (1 - 1 / (4 * (n : ℝ) ^ 2)) ^ (4 * n ^ 3) ≤ Real.exp (-(n : ℝ)) := by
  have h := one_sub_one_div_pow_le_exp_neg (4 * n ^ 2) n (by positivity)
  have hexp : 4 * n ^ 2 * n = 4 * n ^ 3 := by ring
  rw [hexp] at h
  push_cast at h
  exact h

/-- `e^{-n} ≤ (1/2)^n` (the negligible form of the tail bounds, `negligible_two_pow_neg`). -/
theorem exp_neg_le_half_pow (n : ℕ) : Real.exp (-(n : ℝ)) ≤ (1 / 2 : ℝ) ^ n := by
  have h1 : Real.exp (-(n : ℝ)) = Real.exp (-1) ^ n := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [h1]
  apply pow_le_pow_left₀ (Real.exp_pos _).le
  rw [Real.exp_neg]
  have := Real.add_one_le_exp (1 : ℝ)
  rw [inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
  linarith

/-- **Claim 36.2, negligible form**: `(1 - 1/(4n²))^{4n³} ≤ 2^{-n}`. -/
theorem claim_36_2_half_pow (n : ℕ) (hn : 0 < n) :
    (1 - 1 / (4 * (n : ℝ) ^ 2)) ^ (4 * n ^ 3) ≤ (1 / 2 : ℝ) ^ n :=
  (claim_36_2 n hn).trans (exp_neg_le_half_pow n)

/-! ## Prime pairs of bit strings -/

/-- **Prime-pair density on bit strings** [PS10, proof of Theorem 33.5]: for `n ≥ 2`, a
uniform pair of `n`-bit strings reads (`bitsToNat`) as a pair of primes with probability at
least `1/(4n²)` (`NumberTheory.one_div_le_uprob_prime_pair` transported along
`bitsEquiv`). -/
theorem one_div_le_uprob_prime_pair_bits (n : ℕ) (hn : 2 ≤ n) :
    1 / (4 * (n : ℝ) ^ 2) ≤
      uprob (fun z : (Fin n → Bool) × (Fin n → Bool) =>
        (bitsToNat z.1).Prime ∧ (bitsToNat z.2).Prime) := by
  have h := one_div_le_uprob_prime_pair n hn
  rw [← uprob_comp_equiv (Equiv.prodCongr (bitsEquiv n) (bitsEquiv n))] at h
  simpa using h

/-- The uniform subtype of prime pairs of `n`-bit strings is `Π_n × Π_n`: read each string as
a number (`bitsEquiv`) and split the conjunction (`Equiv.subtypeProdEquivProd`). -/
noncomputable def primesPairEquiv (n : ℕ) :
    {z : (Fin n → Bool) × (Fin n → Bool) // (bitsToNat z.1).Prime ∧ (bitsToNat z.2).Prime} ≃
      Primes n × Primes n :=
  (Equiv.subtypeEquiv (Equiv.prodCongr (bitsEquiv n) (bitsEquiv n)) (fun z => by simp)).trans
    Equiv.subtypeProdEquivProd

/-- The components of `primesPairEquiv` are the numbers read from the two strings. -/
@[simp] theorem primesPairEquiv_apply_val (n : ℕ)
    (z : {z : (Fin n → Bool) × (Fin n → Bool) // (bitsToNat z.1).Prime ∧ (bitsToNat z.2).Prime}) :
    ((primesPairEquiv n z).1.1 : ℕ) = bitsToNat z.1.1 ∧
      ((primesPairEquiv n z).2.1 : ℕ) = bitsToNat z.1.2 := by
  simp [primesPairEquiv, Equiv.subtypeProdEquivProd]

/-- `1/|Π_n| ≤ 2n/2^n` for `n ≥ 2` (`NumberTheory.two_pow_le_two_mul_card_primes`): the
probability that two independent uniform primes coincide is negligible. -/
theorem one_div_card_primes_le (n : ℕ) (hn : 2 ≤ n) :
    1 / (Fintype.card (Primes n) : ℝ) ≤ 2 * n / 2 ^ n := by
  have h := two_pow_le_two_mul_card_primes n hn
  have h' : (2 : ℝ) ^ n ≤ 2 * n * Fintype.card (Primes n) := by exact_mod_cast h
  have hpos : (0 : ℝ) < Fintype.card (Primes n) := by
    have : 0 < Fintype.card (Primes n) := by
      by_contra h0
      push_neg at h0
      have : Fintype.card (Primes n) = 0 := by omega
      rw [this, mul_zero] at h
      exact absurd h (not_le.mpr (Nat.two_pow_pos n))
    exact_mod_cast this
  rw [div_le_div_iff₀ hpos (by positivity), one_mul]
  linarith

/-! ## Pairs of distinct primes -/

/-- Pairs of **distinct** primes of `Π_n`: the index distribution of the factoring
assumption and of the RSA/Rabin moduli `N = pq` (decision log "Rabin/RSA scope": `p ≠ q`). -/
abbrev DistinctPrimes (n : ℕ) : Type := {z : Primes n × Primes n // (z.1.1 : ℕ) ≠ z.2.1}

namespace DistinctPrimes

variable {n : ℕ}

/-- The first prime `p`. -/
def p (z : DistinctPrimes n) : ℕ := z.1.1.1

/-- The second prime `q`. -/
def q (z : DistinctPrimes n) : ℕ := z.1.2.1

/-- `p` is prime. -/
theorem p_prime (z : DistinctPrimes n) : z.p.Prime := z.1.1.2

/-- `q` is prime. -/
theorem q_prime (z : DistinctPrimes n) : z.q.Prime := z.1.2.2

/-- `p < 2^n`. -/
theorem p_lt (z : DistinctPrimes n) : z.p < 2 ^ n := z.1.1.1.2

/-- `q < 2^n`. -/
theorem q_lt (z : DistinctPrimes n) : z.q < 2 ^ n := z.1.2.1.2

/-- `p ≠ q`. -/
theorem p_ne_q (z : DistinctPrimes n) : z.p ≠ z.q := z.2

/-- The modulus `N = pq < 2^{2n}`. -/
theorem mul_lt (z : DistinctPrimes n) : z.p * z.q < 2 ^ (2 * n) := by
  rw [two_mul]; exact mul_lt_two_pow_add z.p_lt z.q_lt

/-! ### Instances and the totient (moved from `RSA.lean`, run-3 audit P7-6) -/

/-- The modulus `pq` is nonzero. -/
instance neZero_mul (z : DistinctPrimes n) : NeZero (z.p * z.q) :=
  ⟨mul_ne_zero z.p_prime.ne_zero z.q_prime.ne_zero⟩

/-- `Φ(pq)` is nonzero. -/
instance neZero_totient (z : DistinctPrimes n) : NeZero (Nat.totient (z.p * z.q)) :=
  ⟨(Nat.totient_pos.2 (NeZero.pos _)).ne'⟩

/-- `p` is prime (as a `Fact`). -/
instance fact_p_prime (z : DistinctPrimes n) : Fact z.p.Prime := ⟨z.p_prime⟩

/-- `q` is prime (as a `Fact`). -/
instance fact_q_prime (z : DistinctPrimes n) : Fact z.q.Prime := ⟨z.q_prime⟩

/-- `Φ(pq) = (p−1)(q−1)` for a pair of distinct primes [PS10, p. 47]. -/
theorem totient_mul (z : DistinctPrimes n) : Nat.totient (z.p * z.q) = (z.p - 1) * (z.q - 1) :=
  totient_prime_mul_prime z.p_prime z.q_prime z.p_ne_q

/-- `Φ(pq) ≥ 2`: one of two distinct primes is at least `3`. -/
theorem one_lt_totient (z : DistinctPrimes n) : 1 < Nat.totient (z.p * z.q) := by
  rw [z.totient_mul]
  have hp := z.p_prime.two_le
  have hq := z.q_prime.two_le
  have hne := z.p_ne_q
  rcases Nat.lt_or_ge 2 z.p with h | h
  · calc 1 < 2 * 1 := by norm_num
      _ ≤ (z.p - 1) * (z.q - 1) := Nat.mul_le_mul (by omega) (by omega)
  · have h2 : z.p = 2 := by omega
    have h3 : 3 ≤ z.q := by omega
    calc 1 < 1 * 2 := by norm_num
      _ ≤ (z.p - 1) * (z.q - 1) := Nat.mul_le_mul (by omega) (by omega)

/-- A pair of distinct primes is determined by `(p, q)`. -/
theorem ext {z w : DistinctPrimes n} (hp : z.p = w.p) (hq : z.q = w.q) : z = w := by
  rcases z with ⟨⟨⟨⟨p, hp'⟩, hpp⟩, ⟨⟨q, hq'⟩, hqq⟩⟩, hne⟩
  rcases w with ⟨⟨⟨⟨p', _⟩, _⟩, ⟨⟨q', _⟩, _⟩⟩, _⟩
  simp only [DistinctPrimes.p, DistinctPrimes.q] at hp hq
  subst hp hq
  rfl

/-- `Π_n` has no two distinct primes for `n < 2`. -/
theorem isEmpty_of_lt (hn : n < 2) : IsEmpty (DistinctPrimes n) := by
  refine ⟨fun z => ?_⟩
  have h1 := z.p_prime.two_le
  have h2 := z.q_prime.two_le
  have h3 := z.p_lt
  have h4 := z.q_lt
  have h5 := z.p_ne_q
  interval_cases n <;> omega

/-- The pair `(2, 3)` for `n ≥ 2` (the default element of the collection's domain). -/
def default (hn : 2 ≤ n) : DistinctPrimes n :=
  ⟨(⟨⟨2, lt_of_lt_of_le (by norm_num) ((Nat.pow_le_pow_right (by norm_num) hn).trans_eq' rfl)⟩,
      Nat.prime_two⟩,
    ⟨⟨3, lt_of_lt_of_le (by norm_num) ((Nat.pow_le_pow_right (by norm_num) hn).trans_eq' rfl)⟩,
      Nat.prime_three⟩), (by norm_num : (2 : ℕ) ≠ 3)⟩

end DistinctPrimes

/-! ### Encoding pairs of distinct primes -/

/-- Decode `⟨a, b⟩` as a pair of distinct primes of `Π_m`: both components must be `m`-bit
strings (`decodeFin`) reading as distinct primes; anything else is a failure. -/
def decodeDistinctPrimes (m : ℕ) (w : List Bool) : Option (DistinctPrimes m) :=
  match decodeFin m (pairFstD w), decodeFin m (pairSndD w) with
  | some a, some b =>
    if h : (bitsToNat a).Prime ∧ (bitsToNat b).Prime ∧ bitsToNat a ≠ bitsToNat b then
      some ⟨(⟨⟨bitsToNat a, bitsToNat_lt a⟩, h.1⟩, ⟨⟨bitsToNat b, bitsToNat_lt b⟩, h.2.1⟩), h.2.2⟩
    else none
  | _, _ => none

/-- Encode a pair of distinct primes of `Π_m` as `⟨p, q⟩` with `m`-bit numerals. -/
def encodeDistinctPrimes (m : ℕ) (z : DistinctPrimes m) : List Bool :=
  pairEncode (natToList m z.p) (natToList m z.q)

/-- Decoding inverts encoding. -/
theorem decodeDistinctPrimes_encode (m : ℕ) (z : DistinctPrimes m) :
    decodeDistinctPrimes m (encodeDistinctPrimes m z) = some z := by
  unfold decodeDistinctPrimes encodeDistinctPrimes natToList
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, decodeFin_ofFn,
    bitsToNat_natToBits z.p_lt, bitsToNat_natToBits z.q_lt]
  rw [dif_pos ⟨z.p_prime, z.q_prime, z.p_ne_q⟩]
  congr 1

/-! ## Block rejection sampling on coin lists (run-3 audit P7-6) -/

/-- **Block rejection sampling** on a coin list, the common shape of the honest samplers of
the candidates [PS10, Theorem 53.2 (`Z_N^*`, `Z*_{Φ(N)}`), Theorem 61.7, Theorem 63.10 (Blum
primes), Theorem 52.3 (`Z_q`)]: `T` trials, trial `t` reading the first `k` bits of the
`t`-th block of `B` bits of `r` as a number `v` (`listToNat`), accepted iff `E v`; `none` if
every trial is rejected. With `k ≤ B` and `r` uniform, the `T` values are independent and
uniform below `2^k`, so the output is `firstHit E` on `Fin (2^k)` (`statClose_rejectBlocksL`).
Repair (run-3 audit P7-6): the one sampler behind `sampleUnitL` (RSA, Rabin) and
`samplePrimePL` (Rabin); `sampleBelowL` (discrete log) has the same shape. -/
def rejectBlocksL (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) : Option ℕ :=
  (List.range T).findSome? fun t =>
    if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k))
    else none

/-- An accepted value satisfies the test and is below `2^k` (it is read from at most `k`
bits, `listToNat_lt_two_pow`). -/
theorem rejectBlocksL_spec {E : ℕ → Prop} [DecidablePred E] {k B T : ℕ} {r : List Bool} {v : ℕ}
    (h : rejectBlocksL E k B T r = some v) : E v ∧ v < 2 ^ k := by
  unfold rejectBlocksL at h
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨_, t, _, _, ht, _⟩ := h
  split_ifs at ht with hc
  rw [Option.some.injEq] at ht
  subst ht
  refine ⟨hc, lt_of_lt_of_le (listToNat_lt_two_pow _) ?_⟩
  exact Nat.pow_le_pow_right (by norm_num) (List.length_take_le _ _)

/-- **Block rejection sampling is close to uniform on `E`** (lemma C4 of the chapter 2
inventory on coin lists; the sampling clauses of [PS10, Theorems 52.3, 53.2, 61.7, 63.10]):
for `k ≤ B`, a uniform coin string of `T · B` bits and a default `d < 2^k` with `E d`, the
total sampler `(rejectBlocksL E k B T r).getD d` is within `(1 − Pr_{v < 2^k}[E v])^T` of the
uniform element of `{v < 2^k | E v}`. Repair (run-3 audit P7-6): stated once here instead of
in each consumer.

**Proof sketch.** For `r = List.ofFn r'`, `(r.drop (t·B)).take k = List.ofFn (π_t r')` where
`π_t r'` is the `k`-bit prefix of block `t` (`List.ext_get`, `List.getElem_take`,
`List.getElem_drop`, `List.getElem_ofFn`; the length is `k` since `t < T` and `k ≤ B`), so
`rejectBlocksL E k B T r = (firstHit (fun x : Fin (2^k) => E x) (fun t => bitsEquiv k (π_t r'))).map Fin.val`
(`List.map_coe_finRange`, `List.findSome?_map`, `bitsToNat_eq_listToNat`, `bitsEquiv_val`) and
`(·).getD d = Fin.val ((firstHit …).getD ⟨d, hdk⟩)` (`Option.getD_map`). The map
`r' ↦ (π_t r')_t` from `Fin (T·B) → Bool` to `Fin T → Fin k → Bool` pushes the uniform
distribution to the uniform one — it is the first projection of a splitting equivalence
`(Fin (T·B) → Bool) ≃ (Fin T → Fin k → Bool) × (Fin T → Fin (B − k) → Bool)` (`uprob_comp_equiv`,
`uprob_fst`; alternatively `pushesUniform_of_card_fiber`) — as does
`Equiv.piCongrRight (fun _ => bitsEquiv k)`; conclude from `statClose_firstHit` (default
`⟨d, hdk⟩`, `hd`) by `StatClose.comp_pushesUniform` and `StatClose.map Fin.val`. -/
theorem statClose_rejectBlocksL (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (hkB : k ≤ B)
    {d : ℕ} (hd : E d) (hdk : d < 2 ^ k) :
    StatClose (fun r : Fin (T * B) → Bool => (rejectBlocksL E k B T (List.ofFn r)).getD d)
      (fun e : {v : Fin (2 ^ k) // E (v : ℕ)} => ((e : Fin (2 ^ k)) : ℕ))
      ((1 - uprob fun v : Fin (2 ^ k) => E (v : ℕ)) ^ T) := by
  sorry

end TCSlib.Cryptography.Candidates
