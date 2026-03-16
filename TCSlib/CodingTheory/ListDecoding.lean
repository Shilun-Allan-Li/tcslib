import TCSlib.CodingTheory.Entropy

set_option linter.unusedSectionVars false

/-!
# List Decoding

This file defines list-decodable codes and proves the **list-decoding capacity theorem**:
for any `ρ` with `0 < ρ ≤ 1 − 1/q` and list size `L ≥ 1`, there exist codes of rate

  r = 1 − H_q(ρ) − 1/L

that are list-decodable with radius `ρ` and list size `L`.

## Main Definitions

* `list_decodable ρ hρ₁ hρ₂ n L hL C` : `C` is `(ρ, L)`-list-decodable if every Hamming ball
  of radius `⌊ρn⌋` contains at most `L` codewords of `C`.

## Main Results

* `exists_listDecodable_code` : a counting/probabilistic argument showing existence of
  list-decodable codes meeting a given size bound.
* `binom_ratio_bound` : the ratio `C(N−k, M−k) / C(N,M) ≤ (M/N)ᵏ`.
* `listDecoding_counting_ineq` : the counting inequality used in the capacity proof.
* `list_decoding_capacity` : codes of rate `1 − H_q(ρ) − 1/L` are `(ρ, L)`-list-decodable.

## References

* V. Guruswami, A. Rudra, M. Sudan, "Essential Coding Theory", Chapter on List Decoding.

-/

open Set Filter Asymptotics Finset

namespace CodingTheory
namespace Codeword

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α]
variable {n k : ℕ}

/-- A code `C` is `(ρ, L)`-list-decodable if every Hamming ball of radius `⌊ρn⌋` contains
    at most `L` codewords of `C`. -/
def list_decodable (ρ : ℝ) (hρ₁: 0 ≤ ρ) (hρ₂: ρ ≤ 1) (n L : ℕ) (hL : L ≥ 1) (C : Code n α) : Prop :=
  (∀ y : Codeword n α, (hamming_ball (Nat.floor (ρ*n)) y ∩ C).card ≤ L)

/-- **Existence of list-decodable codes**: if the ball volume `V` and code size `M` satisfy
    the given counting inequality, then there exists a code `C` of size `M` that is
    `(p, L)`-list-decodable. -/
lemma exists_listDecodable_code (n L M : ℕ) (p : ℝ)
  (hp1 : 0 ≤ p) (hp2 : p ≤ 1) (hL : 1 ≤ L)
  (V : ℕ)
  (hV : ∀ y : Codeword n α, (hamming_ball (Nat.floor (p*n)) y).card ≤ V)
  (h_ineq : (Fintype.card α)^n * (Nat.choose V (L+1)) * (Nat.choose ((Fintype.card α)^n - (L+1)) (M - (L+1))) < Nat.choose ((Fintype.card α)^n) M)
  (hM_le_N : M ≤ (Fintype.card α)^n)
  (hL_lt_M : L < M) :
  ∃ C : Code n α, C.card = M ∧ list_decodable p hp1 hp2 n L hL C := by
    contrapose h_ineq;
    have h_bad_codes : ∀ y : Codeword n α, (Finset.filter (fun C => (Finset.filter (fun c => c ∈ C) (hamming_ball ⌊p * n⌋₊ y)).card ≥ L + 1) (Finset.powersetCard M (Finset.univ : Finset (Codeword n α)))).card ≤ Nat.choose V (L + 1) * Nat.choose ((Fintype.card α) ^ n - (L + 1)) (M - (L + 1)) := by
      intro y
      have h_bad_codes_y : (Finset.filter (fun C => (Finset.filter (fun c => c ∈ C) (hamming_ball ⌊p * n⌋₊ y)).card ≥ L + 1) (Finset.powersetCard M (Finset.univ : Finset (Codeword n α)))).card ≤ (Finset.powersetCard (L + 1) (hamming_ball ⌊p * n⌋₊ y)).card * Nat.choose ((Fintype.card α) ^ n - (L + 1)) (M - (L + 1)) := by
        refine' le_trans ( Finset.card_le_card _ ) _;
        exact Finset.biUnion ( Finset.powersetCard ( L + 1 ) ( hamming_ball ⌊p * n⌋₊ y ) ) fun S => Finset.image ( fun T => S ∪ T ) ( Finset.powersetCard ( M - ( L + 1 ) ) ( Finset.univ \ S ) );
        · intro C hC; simp_all +decide [ Finset.subset_iff ] ;
          obtain ⟨ S, hS ⟩ := Finset.exists_subset_card_eq hC.2;
          refine' ⟨ S, ⟨ fun x hx => _, hS.2 ⟩, C \ S, ⟨ fun x hx => _, _ ⟩, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
          grind;
        · refine' le_trans ( Finset.card_biUnion_le ) _;
          refine' le_trans ( Finset.sum_le_sum fun x hx => Finset.card_image_le ) _;
          simp +decide [ Finset.card_sdiff ];
          refine' le_trans ( Finset.sum_le_sum fun x hx => Nat.choose_le_choose _ _ ) _;
          rotate_left;
          use fun x => Fintype.card α ^ n - ( L + 1 );
          · simp +decide [ Finset.card_powersetCard ];
          · grind;
      refine' le_trans h_bad_codes_y _;
      exact Nat.mul_le_mul_right _ ( by rw [ Finset.card_powersetCard ] ; exact Nat.choose_le_choose _ ( hV y ) );
    have h_bad_codes_count : (Finset.filter (fun C => ∃ y : Codeword n α, (Finset.filter (fun c => c ∈ C) (hamming_ball ⌊p * n⌋₊ y)).card ≥ L + 1) (Finset.powersetCard M (Finset.univ : Finset (Codeword n α)))).card ≤ (Fintype.card α) ^ n * Nat.choose V (L + 1) * Nat.choose ((Fintype.card α) ^ n - (L + 1)) (M - (L + 1)) := by
      have h_bad_codes_count : (Finset.filter (fun C => ∃ y : Codeword n α, (Finset.filter (fun c => c ∈ C) (hamming_ball ⌊p * n⌋₊ y)).card ≥ L + 1) (Finset.powersetCard M (Finset.univ : Finset (Codeword n α)))).card ≤ (∑ y : Codeword n α, (Finset.filter (fun C => (Finset.filter (fun c => c ∈ C) (hamming_ball ⌊p * n⌋₊ y)).card ≥ L + 1) (Finset.powersetCard M (Finset.univ : Finset (Codeword n α)))).card) := by
        have h_bad_codes_count : (Finset.filter (fun C => ∃ y : Codeword n α, (Finset.filter (fun c => c ∈ C) (hamming_ball ⌊p * n⌋₊ y)).card ≥ L + 1) (Finset.powersetCard M (Finset.univ : Finset (Codeword n α)))).card ≤ (Finset.biUnion (Finset.univ : Finset (Codeword n α)) (fun y => Finset.filter (fun C => (Finset.filter (fun c => c ∈ C) (hamming_ball ⌊p * n⌋₊ y)).card ≥ L + 1) (Finset.powersetCard M (Finset.univ : Finset (Codeword n α))))).card := by
          exact Finset.card_le_card fun x hx => by aesop;
        exact h_bad_codes_count.trans ( Finset.card_biUnion_le );
      refine' le_trans h_bad_codes_count ( le_trans ( Finset.sum_le_sum fun _ _ => h_bad_codes _ ) _ );
      simp +decide [ mul_assoc, Fintype.card_pi ];
    simp_all +decide [ list_decodable ];
    refine' le_trans _ h_bad_codes_count;
    rw [ Finset.filter_true_of_mem ];
    · simp +decide [ Finset.card_univ ];
    · intro C hC; specialize h_ineq C; aesop;

/-- **Binomial ratio bound**: `C(N−k, M−k) / C(N, M) ≤ (M/N)ᵏ`. -/
lemma binom_ratio_bound (N M k : ℕ) (hM : M ≤ N) (hk : k ≤ M) :
  (Nat.choose (N - k) (M - k) : ℝ) / (Nat.choose N M) ≤ ((M : ℝ) / N) ^ k := by
    have h_prod : ((Nat.choose (N - k) (M - k)) : ℝ) / (Nat.choose N M) = Finset.prod (Finset.range k) (fun i => ((M - i) : ℝ) / ((N - i) : ℝ)) := by
      rw [ div_eq_iff ];
      · have h_binom : (Nat.choose (N - k) (M - k) : ℝ) * (Nat.choose N k : ℝ) = (Nat.choose N M : ℝ) * (Nat.choose M k : ℝ) := by
          rw_mod_cast [ Nat.choose_mul ] <;> try omega;
          ring;
        have h_binom_fact : (Nat.choose M k : ℝ) = (∏ i ∈ Finset.range k, (M - i : ℝ)) / (Nat.factorial k) ∧ (Nat.choose N k : ℝ) = (∏ i ∈ Finset.range k, (N - i : ℝ)) / (Nat.factorial k) := by
          constructor <;> rw [ eq_div_iff ( by positivity ) ];
          · rw_mod_cast [ mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ];
            rw [ Nat.descFactorial_eq_prod_range ];
            rw [ Nat.cast_prod, Finset.prod_congr rfl fun x hx => Int.subNatNat_of_le ( by linarith [ Finset.mem_range.mp hx ] ) ];
          · rw_mod_cast [ mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ];
            rw [ Nat.descFactorial_eq_prod_range ];
            rw [ Nat.cast_prod, Finset.prod_congr rfl fun x hx => Int.subNatNat_of_le ( by linarith [ Finset.mem_range.mp hx ] ) ];
        by_cases h : ( ∏ i ∈ Finset.range k, ( N - i : ℝ ) ) = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_comm, Finset.prod_mul_distrib ];
        · exact absurd h_binom_fact.2 <| ne_of_gt <| Nat.choose_pos <| by linarith;
        · field_simp at *;
          convert h_binom using 1;
      · exact ne_of_gt <| Nat.cast_pos.mpr <| Nat.choose_pos hM;
    have h_le : ∀ i ∈ Finset.range k, ((M - i) : ℝ) / ((N - i) : ℝ) ≤ (M : ℝ) / N := by
      intro i hi; rw [ div_le_div_iff₀ ] <;> nlinarith only [ show ( i : ℝ ) + 1 ≤ M by norm_cast; linarith [ Finset.mem_range.mp hi ], show ( M : ℝ ) ≤ N by norm_cast ] ;
    simpa only [ h_prod, Finset.prod_const, Finset.card_range ] using Finset.prod_le_prod ( fun _ _ => div_nonneg ( sub_nonneg.2 <| Nat.cast_le.2 <| by linarith [ Finset.mem_range.1 ‹_› ] ) ( sub_nonneg.2 <| Nat.cast_le.2 <| by linarith [ Finset.mem_range.1 ‹_› ] ) ) h_le

/-- **Counting inequality for list decoding**: for the given choice of rate `r` and ball-size
    bound `V`, the number of "bad" `M`-subsets exceeds the number of good ones only if `M` is
    small (i.e., rate > capacity). -/
lemma listDecoding_counting_ineq
  (q : ℕ) (p : ℝ) (n L : ℕ)
  (hq : 2 ≤ q)
  (hL : 1 ≤ L)
  (r : ℝ) (hr : r = 1 - (qaryEntropy q p) - 1 / (L : ℝ))
  (M : ℕ) (hM : M = Nat.floor ((q : ℝ) ^ (r * n)))
  (V : ℕ) (hV : V = Nat.floor (Real.rpow q ((qaryEntropy q p) * n)))
  (hM_pos : 0 < M)
  (hM_le : M ≤ q^n)
  (hL_lt_M : L < M) :
  (q : ℝ)^n * (Nat.choose V (L+1)) * (Nat.choose (q^n - (L+1)) (M - (L+1))) < Nat.choose (q^n) M := by
    have h_binom_ratio : (Nat.choose (q ^ n - (L + 1)) (M - (L + 1)) : ℝ) / (Nat.choose (q ^ n) M) ≤ ((M : ℝ) / (q ^ n)) ^ (L + 1) := by
      convert binom_ratio_bound ( q ^ n ) M ( L + 1 ) _ _ using 1;
      · norm_cast;
      · linarith;
      · linarith;
    have h_binom_bound : (Nat.choose V (L + 1) : ℝ) ≤ (V : ℝ) ^ (L + 1) / (Nat.factorial (L + 1)) := by
      exact Nat.choose_le_pow_div (L + 1) V;
    have h_combined : (q ^ n : ℝ) * ((V : ℝ) ^ (L + 1) / (Nat.factorial (L + 1))) * ((M : ℝ) / (q ^ n)) ^ (L + 1) < 1 := by
      have h_simplified : (q : ℝ) ^ (-n / (L : ℝ)) / (Nat.factorial (L + 1)) < 1 := by
        rw [ div_lt_iff₀ ] <;> norm_num [ Nat.factorial_pos ];
        exact lt_of_le_of_lt ( Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) <| div_nonpos_of_nonpos_of_nonneg ( neg_nonpos.mpr <| Nat.cast_nonneg _ ) <| Nat.cast_nonneg _ ) <| by norm_num; linarith [ show ( L + 1 : ℝ ) ≥ 2 by norm_cast; linarith, show ( Nat.factorial ( L + 1 ) : ℝ ) ≥ L + 1 by exact_mod_cast Nat.self_le_factorial _ ] ;
      have h_subst : (q : ℝ) ^ n * ((q : ℝ) ^ (qaryEntropy q p * n)) ^ (L + 1) * ((q : ℝ) ^ (r * n) / (q ^ n)) ^ (L + 1) / (Nat.factorial (L + 1)) < 1 := by
        convert h_simplified using 1 ; rw [ hr ] ; ring_nf ; norm_num [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg q ) ] ; ring_nf;
        norm_num [ Real.rpow_add ( by positivity : 0 < ( q : ℝ ) ), Real.rpow_sub ( by positivity : 0 < ( q : ℝ ) ), Real.rpow_neg ( by positivity : 0 ≤ ( q : ℝ ) ) ] ; ring_nf;
        field_simp
        ring_nf;
        norm_cast ; norm_num [ pow_mul', mul_assoc, ne_of_gt ( zero_lt_two.trans_le hq ) ];
        rw [ ← div_eq_mul_inv, div_eq_iff ( by positivity ) ] ; ring;
      refine' lt_of_le_of_lt _ h_subst;
      rw [ mul_div_right_comm ];
      rw [ mul_div_assoc ];
      gcongr;
      · exact_mod_cast hV.symm ▸ Nat.floor_le ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ );
      · exact_mod_cast hM.symm ▸ Nat.floor_le ( by positivity );
    rw [ div_le_iff₀ ] at h_binom_ratio;
    · refine' lt_of_le_of_lt ( mul_le_mul_of_nonneg_left h_binom_ratio <| by positivity ) _;
      refine' lt_of_le_of_lt ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left h_binom_bound <| by positivity ) <| by positivity ) _;
      convert mul_lt_mul_of_pos_right h_combined ( Nat.cast_pos.mpr <| Nat.choose_pos hM_le ) using 1 ; ring;
      ring;
    · exact Nat.cast_pos.mpr ( Nat.choose_pos hM_le )

/-- **List-decoding capacity theorem**: for any `0 < ρ ≤ 1 − 1/q` and `L ≥ 1`, there exist
    codes of rate `r = 1 − H_q(ρ) − 1/L` that are `(ρ, L)`-list-decodable.

    In other words, one can list-decode at any rate below the list-decoding capacity
    `1 − H_q(ρ)` using list size `L`. -/
theorem list_decoding_capacity
  (q : ℕ) (p : ℝ) (hq : q = (Fintype.card α)) (hp : 0 < p ∧ p ≤ 1 - 1/q)
  (L : ℕ) (hL : 1 ≤ L) :
  let r := 1 - (qaryEntropy q p) - 1 / (L : ℝ)
  let M := Nat.floor ((q : ℝ) ^ (r * n))
  ∃ C : Code n α,
    (M ≤ C.card) ∧
      list_decodable p
        (by linarith [hp])
        (by
          linarith [hp,
            one_div_nonneg.2 (show (0 : ℝ) ≤ (q : ℝ) from by exact_mod_cast (Nat.zero_le q))])
        n L hL C := by
  classical
  intro r M

  have hq2 : 2 ≤ q := by
    rw [hq]
    exact Nat.succ_le_iff.mpr (by simpa using Fintype.one_lt_card)
  have hq_pos : (1 : ℝ) < (q : ℝ) := by
    exact natCast_one_lt_of_two_le hq2
  have hq_ge_0 : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.zero_le q)
  have hq_ge_1 : (1 : ℝ) ≤ (q : ℝ) := by linarith

  have hr : r ≤ 1 := by
    have hH : 0 < qaryEntropy q p := qary_entropy_pos q p hq hp
    have hL0 : 0 ≤ 1 / (L : ℝ) := by
      have : (0 : ℝ) < (L : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (Nat.succ_pos 0) hL)
      exact one_div_nonneg.mpr (le_of_lt this)
    dsimp [r]
    linarith

  have exists_code_card_eq
    (hM : M ≤ Fintype.card (Codeword n α)) :
    ∃ C : Code n α, C.card = M := by
    classical
    obtain ⟨S, hSsub, hScard⟩ :=
      Finset.exists_subset_card_eq hM (s := (Finset.univ : Finset (Codeword n α)))
    refine ⟨S, ?_⟩
    simpa using hScard

  by_cases hML : M ≤ L
  · have hM_le_univ : M ≤ Fintype.card (Codeword n α) := by
      have : Fintype.card (Codeword n α) = q^n := by
        simp [Codeword, hq, Fintype.card_pi]
      have hM_le_qn : M ≤ q^n := by
        have h_rn : r * (n : ℝ) ≤ (n : ℝ) := by nlinarith [hr]
        have hpow :
          (q : ℝ) ^ (r * (n : ℝ)) ≤ (q : ℝ) ^ ((n : ℝ)) := by
            exact Real.rpow_le_rpow_of_exponent_le hq_ge_1 h_rn
        have hfloor_le :
          (M : ℝ) ≤ (q : ℝ) ^ (r * (n : ℝ)) := by
          simpa using (Nat.floor_le (Real.rpow_nonneg hq_ge_0 (r * (n : ℝ))))
        have : (M : ℝ) ≤ (q : ℝ) ^ ((n : ℝ)) := le_trans hfloor_le hpow
        have : (M : ℝ) ≤ (q^n : ℝ) := by simpa [Real.rpow_natCast] using this
        exact_mod_cast this
      simpa [this] using hM_le_qn

    rcases exists_code_card_eq hM_le_univ with ⟨C, hCcard⟩
    refine ⟨C, ?_, ?_⟩
    · simp [hCcard]
    · unfold list_decodable
      intro y
      have hleC : (hamming_ball (Nat.floor (p * n)) y ∩ C).card ≤ C.card := by
        exact Finset.card_le_card (Finset.inter_subset_right)
      have : (hamming_ball (Nat.floor (p * n)) y ∩ C).card ≤ L := by
        rw [← hCcard] at hML
        simpa [hCcard] using le_trans hleC hML
      exact this

  · have hL_lt_M : L < M := Nat.lt_of_not_ge hML

    let N : ℕ := q^n
    let V : ℕ := Nat.floor (Real.rpow q ((qaryEntropy q p) * n))

    have hV_def : V = Nat.floor (Real.rpow q ((qaryEntropy q p) * n)) := by rfl

    have hM_le : M ≤ q^n := by
      have h_rn : r * (n : ℝ) ≤ (n : ℝ) := by nlinarith [hr]
      have hpow :
        (q : ℝ) ^ (r * (n : ℝ)) ≤ (q : ℝ) ^ ((n : ℝ)) := by
        exact Real.rpow_le_rpow_of_exponent_le hq_ge_1 h_rn
      have hfloor_le :
        (M : ℝ) ≤ (q : ℝ) ^ (r * (n : ℝ)) := by
        simpa using (Nat.floor_le (Real.rpow_nonneg hq_ge_0 (r * (n : ℝ))))
      have : (M : ℝ) ≤ (q : ℝ) ^ ((n : ℝ)) := le_trans hfloor_le hpow
      have : (M : ℝ) ≤ (q^n : ℝ) := by simpa [Real.rpow_natCast] using this
      exact_mod_cast this

    have hM_pos : 0 < M := by
        linarith

    have hV_ball :
    ∀ y : Codeword n α, (hamming_ball (Nat.floor (p * n)) y).card ≤ V := by
      intro y
      have hball_real :
        (hamming_ball (Nat.floor (p * n)) y).card ≤ Real.rpow q (qaryEntropy q p * n) := by
        have hα : Nontrivial α := inferInstance
        have hradius : Nat.floor (p * n) = ⌊(n : ℝ) * p⌋₊ := by
          simp [mul_comm]
        simpa [hradius] using (hamming_ball_size_asymptotic_upper_bound q n p hq hα hp) y
      have : ((hamming_ball (Nat.floor (p * n)) y).card : ℝ) ≤ Real.rpow q (qaryEntropy q p * n) := by
        exact_mod_cast hball_real
      exact (Nat.le_floor this)

    have hr_def : r = 1 - (qaryEntropy q p) - 1 / (L : ℝ) := rfl
    have hM_def : M = Nat.floor ((q : ℝ) ^ (r * n)) := rfl

    have h_ineq :
      (q : ℝ)^n * (Nat.choose V (L+1)) * (Nat.choose (q^n - (L+1)) (M - (L+1)))
        < Nat.choose (q^n) M := by
      refine listDecoding_counting_ineq q p n L hq2 hL r hr_def M hM_def V hV_def
        (by exact hM_pos)
        hM_le
        hL_lt_M

    have h_ineq_nat :
        (Fintype.card α)^n
            * Nat.choose V (L+1)
            * Nat.choose ((Fintype.card α)^n - (L+1)) (M - (L+1))
        < Nat.choose ((Fintype.card α)^n) M := by
        have h_ineq_real :
            ((Fintype.card α)^n : ℝ)
            * (Nat.choose V (L+1) : ℝ)
            * (Nat.choose ((Fintype.card α)^n - (L+1)) (M - (L+1)) : ℝ)
            < (Nat.choose ((Fintype.card α)^n) M : ℝ) := by
            simpa [Nat.cast_pow, hq] using h_ineq
        exact_mod_cast h_ineq_real

    have hp1 : 0 ≤ p := le_of_lt hp.1
    have hp2 : p ≤ 1 := by
      exact le_of_lt (lt_one_of_le_one_sub_inv (natCast_pos_of_two_le hq2) hp.2)

    obtain ⟨C, hCcard, hCld⟩ :=
        exists_listDecodable_code (n := n) (L := L) (M := M) (p := p)
            hp1 hp2 hL
            V hV_ball
            h_ineq_nat
            (by simpa [hq] using hM_le)
            hL_lt_M

    refine ⟨C, ?_, hCld⟩
    simp [hCcard]

end Codeword
end CodingTheory
