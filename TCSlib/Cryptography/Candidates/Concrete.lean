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
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
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
* `TCSlib.Cryptography.Candidates.rejectBlocksL_eq_find?` — block rejection sampling as a
  search followed by the value read.
* `TCSlib.Cryptography.Candidates.polyTimeComputable_rejectBlocksL` — block rejection sampling
  is polynomial-time (host H15; statement only, its proof is an open fill).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.3.1–§2.3.2, Theorem 33.5, Algorithm 33.6; §2.4.2, Claim 36.2, Theorem 36.3,
  Algorithm 37.4; §2.7, Theorem 51.1; Theorems 52.3, 53.2, 61.7 and 63.10, the samplers of
  block rejection sampling.)
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
  simp only [uprob_def]
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
      rw [uprob_def]
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
  rw [invProb_def]
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
          have hfi := congrFun h i
          rw [OneWay.prodFun_apply, OneWay.prodFun_apply] at hfi
          exact Or.inr ⟨i, mem_univ _, hi, hfi⟩
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
            simp [yaoTry_eq, prodFun_update]
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

/-- The defining equation of `DistinctPrimes.p`: `z.p` is the value of the first prime of the
pair, `z.p = ((z.1.1 : Fin (2^n)) : ℕ)`. -/
theorem p_eq (z : DistinctPrimes n) : z.p = ((z.1.1 : Fin (2 ^ n)) : ℕ) := rfl

/-- The second prime `q`. -/
def q (z : DistinctPrimes n) : ℕ := z.1.2.1

/-- The defining equation of `DistinctPrimes.q`: `z.q` is the value of the second prime of the
pair, `z.q = ((z.1.2 : Fin (2^n)) : ℕ)`. -/
theorem q_eq (z : DistinctPrimes n) : z.q = ((z.1.2 : Fin (2 ^ n)) : ℕ) := rfl

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

/-- The first prime of the default pair is `2`: `(DistinctPrimes.default hn).p = 2`. -/
theorem default_p (hn : 2 ≤ n) : (DistinctPrimes.default hn).p = 2 := rfl

/-- The second prime of the default pair is `3`: `(DistinctPrimes.default hn).q = 3`. -/
theorem default_q (hn : 2 ≤ n) : (DistinctPrimes.default hn).q = 3 := rfl

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

/-- The defining equation of `encodeDistinctPrimes`:
`encodeDistinctPrimes m z = ⟨⟦p⟧_m, ⟦q⟧_m⟩`, the pair of the `m`-bit numerals of the two primes. -/
theorem encodeDistinctPrimes_eq (m : ℕ) (z : DistinctPrimes m) :
    encodeDistinctPrimes m z = pairEncode (natToList m z.p) (natToList m z.q) := rfl

/-- Decoding inverts encoding. -/
theorem decodeDistinctPrimes_encode (m : ℕ) (z : DistinctPrimes m) :
    decodeDistinctPrimes m (encodeDistinctPrimes m z) = some z := by
  unfold decodeDistinctPrimes encodeDistinctPrimes
  rw [natToList_eq, natToList_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, decodeFin_ofFn,
    bitsToNat_natToBits z.p_lt, bitsToNat_natToBits z.q_lt]
  rw [dif_pos ⟨z.p_prime, z.q_prime, z.p_ne_q⟩]
  congr 1

/-- **Decoding is canonical**: a string that `decodeDistinctPrimes m` decodes to `z` is
`encodeDistinctPrimes m z` (the clause `Collection.encD_decD` of the factoring collection;
gate 03b, finding 1).

**Proof sketch.** Both components decode as `m`-bit strings `a`, `b`, so they are `List.ofFn a`,
`List.ofFn b` (`ofFn_of_decodeFin_eq_some`), the numerals of `p = bitsToNat a`, `q = bitsToNat b`
at width `m` (`natToList_length_listToNat`); the first is nonempty (`Π_m` has two distinct
primes only for `m ≥ 2`, `DistinctPrimes.isEmpty_of_lt`), so the string is the pair of its
components (`eq_pairEncode_of_pairFstD_ne`). -/
theorem encodeDistinctPrimes_of_decode {m : ℕ} {w : List Bool} {z : DistinctPrimes m}
    (h : decodeDistinctPrimes m w = some z) : encodeDistinctPrimes m z = w := by
  have hm : 2 ≤ m := by
    by_contra hm
    exact (DistinctPrimes.isEmpty_of_lt (not_le.1 hm)).false z
  have hnum : ∀ a : Fin m → Bool, natToList m (bitsToNat a) = List.ofFn a := fun a => by
    have := natToList_length_listToNat (List.ofFn a)
    rwa [List.length_ofFn, ← bitsToNat_eq_listToNat] at this
  unfold decodeDistinctPrimes at h
  rcases ha : decodeFin m (pairFstD w) with _ | a <;> rcases hb : decodeFin m (pairSndD w) with _ | b <;>
    simp only [ha, hb, reduceCtorEq] at h
  split_ifs at h with hc
  obtain rfl := Option.some.inj h
  have hne : pairFstD w ≠ [] := fun h0 => by
    have := length_eq_of_decodeFin_eq_some ha
    rw [h0, List.length_nil] at this
    omega
  show pairEncode (natToList m (bitsToNat a)) (natToList m (bitsToNat b)) = w
  rw [hnum, hnum, ofFn_of_decodeFin_eq_some ha, ofFn_of_decodeFin_eq_some hb]
  exact (eq_pairEncode_of_pairFstD_ne hne).symm

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

/-- Block rejection sampling unfolded: `rejectBlocksL E k B T r` is the first `some v` over
`t ∈ [0, T)` (`List.findSome?` over `List.range T`) with `v` the number read from the first `k`
bits of the `t`-th block of `B` bits of `r`, kept iff `E v`. -/
theorem rejectBlocksL_eq (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) :
    rejectBlocksL E k B T r = (List.range T).findSome? fun t =>
      if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k))
      else none :=
  rfl

/-- **Block rejection sampling as a search followed by the value read**: `rejectBlocksL E k B T r`
is the first trial `t < T` whose value `v_t = ⟦(r.drop (t B)).take k⟧` passes `E`, mapped to
`v_t`:
`rejectBlocksL E k B T r = ((List.range T).find? fun t => decide (E v_t)).map fun t => v_t`
(core `List.findSome?_guard`, `List.map_findSome?`, `Option.guard_apply`). -/
theorem rejectBlocksL_eq_find? (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) :
    rejectBlocksL E k B T r =
      ((List.range T).find? fun t => decide (E (listToNat ((r.drop (t * B)).take k)))).map
        fun t => listToNat ((r.drop (t * B)).take k) := by
  rw [rejectBlocksL_eq, ← List.findSome?_guard, List.map_findSome?]
  congr 1
  funext t
  rw [Function.comp_apply, Option.guard_apply]
  by_cases ht : E (listToNat ((r.drop (t * B)).take k))
  · rw [if_pos ht, decide_eq_true ht, if_pos rfl, Option.map_some]
  · rw [if_neg ht, decide_eq_false ht, if_neg Bool.false_ne_true, Option.map_none]

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

/-- **Block rejection sampling is polynomial-time** (host H15) [PS10, Theorems 52.3, 53.2, 61.7
and 63.10: "the domain is easy to sample"]. Let `E a v` be a test on a parameter `a` and a value
`v`, decided on words by a polynomial-time bit `acc`, so that `acc ⟨w, b⟩ = [E ⟦w⟧ ⟦b⟧]`. Take
polynomial-time words `par z` (the parameter), `kw z`, `bw z` and `tw z`, whose lengths are the
trial width `k`, the block length `B` and the trial count `T`, and `c z` (the coins). Then some
polynomial-time `g` computes the sampler `rejectBlocksL (E ⟦par z⟧) k B T (c z)`:
- `g z = []` when every trial is rejected;
- otherwise `g z = true :: b`, where `b` reads as the accepted value and has at most `k` bits.

That is, `(g z).tail.length ≤ k` and
`rejectBlocksL (E ⟦par z⟧) k B T (c z) = if g z = [] then none else some ⟦(g z).tail⟧`.
In particular `(rejectBlocksL …).getD 0 = ⟦(g z).tail⟧`, since `[].tail = []` reads as `0`
(`listToNat_nil`). The statement is existential: the trial loop that realizes it is internal,
and no consumer reads it.

**Deviation:** [PS10] samples these domains exactly, in expected polynomial time; here the
sampler is truncated to `T` trials (deviations register #15, `statClose_rejectBlocksL` carries
the statistical term), and the host states only the polynomial-time computability of that
truncated sampler on strings.

**Proof sketch.**
- **The loop.** The state is `⟨⟨⟨1^B, 1^k⟩, w⟩, ⟨1^T, r⟩⟩`, with `w = par z` and `r = c z`. One
  step keeps the header `⟨⟨1^B, 1^k⟩, w⟩`, drops one bit of the counter `1^T` and one block of
  `B` coins (`polyTimeComputable_tail`, `polyTimeComputable_pairDropPoly`). The trial word is
  the first `k` coins (`polyTimeComputable_pairTakePoly`). The test accepts iff the counter is
  nonempty and `acc ⟨w, trial word⟩` holds (`polyTimeComputable_isNil`, `polyTimeComputable_not`,
  `polyTimeComputable_and`, with the tests given explicitly). The payload is `true` followed by
  the trial word (`polyTimeComputable_prepend`). The start state is assembled from the given
  words (`polyTimeComputable_unaryPoly`, or `List.replicate` of the lengths, and
  `PolyTimeComputable.pairEncode`), and `g` is the loop on it, in applied form
  (`PolyTimeComputable.comp'`).
- **Polynomial time.** One step at most doubles the length (`|step x| ≤ 2|x| + 4`), and from the
  second step on the state is a well-formed pair that only shrinks
  (`StateLoop.length_pairFstD_add_pairSndD_le`), so every orbit point has length at most
  `2|x| + 4`. The repetition host `Complexity.polyTimeComputable_iterateFind`, with `R = var` and
  orbit bound `2n + 4`, therefore makes the loop polynomial-time. Its `match` on the search
  result is split by `split` (its equation lemmas), never matched by definitional unfolding.
- **Correctness.** After `i` steps the state is `⟨h, ⟨1^T.drop i, r.drop (i B)⟩⟩` (induction on
  `i`, `List.drop_drop`), so trial `i` reads the `k`-bit prefix `v_i = ⟦(r.drop (i B)).take k⟧`
  of block `i`, and the test at step `i` is `i < T ∧ E ⟦w⟧ v_i` (`hspec`). The search over the
  first `|start| + 1 ≥ T` rounds is therefore the search over `[0, T)`
  (`IterateFind.find?_range_and_lt`), which is `rejectBlocksL` read as a search followed by its
  value (`rejectBlocksL_eq_find?`). If the search fails, `g z = []`; otherwise
  `g z = true :: trial word`, whose tail has at most `k` bits (`List.length_take_le`) and reads
  as the accepted value. -/
theorem polyTimeComputable_rejectBlocksL (E : ℕ → ℕ → Prop) [∀ a, DecidablePred (E a)]
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun x => [acc x])
    (hspec : ∀ w b : List Bool, acc (pairEncode w b) = decide (E (listToNat w) (listToNat b)))
    {par kw bw tw c : List Bool → List Bool} (hpar : PolyTimeComputable par)
    (hkw : PolyTimeComputable kw) (hbw : PolyTimeComputable bw) (htw : PolyTimeComputable tw)
    (hc : PolyTimeComputable c) :
    ∃ g : List Bool → List Bool, PolyTimeComputable g ∧ ∀ z,
      (g z).tail.length ≤ (kw z).length ∧
      rejectBlocksL (E (listToNat (par z))) (kw z).length (bw z).length (tw z).length (c z) =
        if g z = [] then none else some (listToNat (g z).tail) := by
  sorry

/-- The position of bit `j < k` of block `t < T` in a string of `T · B` coins (`k ≤ B`):
`t · B + j`. -/
private def dla_blockPos {k B T : ℕ} (hkB : k ≤ B) (p : Fin T × Fin k) : Fin (T * B) :=
  ⟨p.1.val * B + p.2.val, by
    have h1 := p.1.2
    have h2 := p.2.2
    calc p.1.val * B + p.2.val < p.1.val * B + B := by omega
      _ = (p.1.val + 1) * B := by ring
      _ ≤ T * B := Nat.mul_le_mul_right _ h1⟩

/-- Distinct (block, bit) pairs sit at distinct coin positions (`j < k ≤ B`). -/
private theorem dla_blockPos_injective {k B T : ℕ} (hkB : k ≤ B) :
    Function.Injective (dla_blockPos (T := T) hkB) := by
  rintro ⟨t, j⟩ ⟨t', j'⟩ h
  have h' : t.val * B + j.val = t'.val * B + j'.val := congrArg Fin.val h
  have hj := j.2
  have hj' := j'.2
  have hB : 0 < B := lt_of_lt_of_le (Nat.zero_lt_of_lt hj) hkB
  have ht : t.val = t'.val := by
    have e1 : (t.val * B + j.val) / B = t.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt (by omega), zero_add]
    have e2 : (t'.val * B + j'.val) / B = t'.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt (by omega), zero_add]
    rw [← e1, ← e2, h']
  have hj2 : j.val = j'.val := by rw [ht] at h'; omega
  rw [Fin.ext ht, Fin.ext hj2]

/-- The `k`-bit prefix of block `t` of a coin string, read off the list: for `t < T` and
`k ≤ B`, `((List.ofFn r).drop (t · B)).take k = List.ofFn (fun j => r (t · B + j))`. -/
private theorem dla_take_drop_ofFn {k B T : ℕ} (hkB : k ≤ B) (r : Fin (T * B) → Bool) (t : Fin T) :
    ((List.ofFn r).drop (t.val * B)).take k =
      List.ofFn (fun j : Fin k => r (dla_blockPos hkB (t, j))) := by
  have hlen : t.val * B + k ≤ T * B := by
    have := t.2
    calc t.val * B + k ≤ t.val * B + B := by omega
      _ = (t.val + 1) * B := by ring
      _ ≤ T * B := Nat.mul_le_mul_right _ this
  apply List.ext_getElem
  · rw [List.length_take, List.length_drop, List.length_ofFn, List.length_ofFn]
    omega
  · intro j h1 h2
    rw [List.getElem_take, List.getElem_drop, List.getElem_ofFn, List.getElem_ofFn]
    rfl

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
  -- the numbers read from the blocks, as a uniform draw of `T` elements of `Fin (2^k)`
  let π : (Fin (T * B) → Bool) → Fin T → Fin (2 ^ k) :=
    fun r t => bitsEquiv k (fun j => r (dla_blockPos hkB (t, j)))
  have hπ : HardcoreBit.PushesUniform π := by
    have h1 :=
      HardcoreBit.pushesUniform_restrict (O := Bool) (dla_blockPos_injective (T := T) hkB)
    have h2 := HardcoreBit.pushesUniform_equiv
      ((Equiv.curry (Fin T) (Fin k) Bool).trans (Equiv.piCongrRight fun _ : Fin T => bitsEquiv k))
    exact h1.comp h2
  have h := ((statClose_firstHit (fun v : Fin (2 ^ k) => E (v : ℕ)) T
    (d := ⟨d, hdk⟩) hd).comp_pushesUniform hπ).map Fin.val
  -- the block sampler is the first hit of the numbers read, mapped to `ℕ`
  have hX : ∀ r : Fin (T * B) → Bool, (rejectBlocksL E k B T (List.ofFn r)).getD d =
      ((firstHit (fun v : Fin (2 ^ k) => E (v : ℕ)) (π r)).getD ⟨d, hdk⟩).val := by
    intro r
    have hmap : rejectBlocksL E k B T (List.ofFn r) =
        (firstHit (fun v : Fin (2 ^ k) => E (v : ℕ)) (π r)).map Fin.val := by
      rw [rejectBlocksL_eq, firstHit_eq, List.map_findSome?, ← List.map_coe_finRange,
        List.findSome?_map]
      congr 1
      funext t
      have hv : listToNat (((List.ofFn r).drop (t.val * B)).take k) = (π r t).val := by
        rw [dla_take_drop_ofFn hkB r t, bitsEquiv_val, bitsToNat_eq_listToNat]
      show (if E (listToNat (((List.ofFn r).drop (t.val * B)).take k)) then
          some (listToNat (((List.ofFn r).drop (t.val * B)).take k)) else none) =
        Option.map Fin.val (if E (π r t).val then some (π r t) else none)
      rw [hv]
      by_cases hE : E (π r t).val
      · rw [if_pos hE, if_pos hE, Option.map_some]
      · rw [if_neg hE, if_neg hE, Option.map_none]
    rw [hmap]
    exact Option.getD_map Fin.val ⟨d, hdk⟩ _
  have hX' : (fun r : Fin (T * B) → Bool => (rejectBlocksL E k B T (List.ofFn r)).getD d) =
      fun r => ((firstHit (fun v : Fin (2 ^ k) => E (v : ℕ)) (π r)).getD ⟨d, hdk⟩).val :=
    funext hX
  rw [hX']
  exact h

end TCSlib.Cryptography.Candidates
