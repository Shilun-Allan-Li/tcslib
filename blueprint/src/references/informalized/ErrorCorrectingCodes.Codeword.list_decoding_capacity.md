<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/ListDecoding.lean :: list_decoding_capacity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# List-decoding capacity

**Claim.** Let `q = Fintype.card α`, `0 < p ≤ 1 - 1/q`, and `L ≥ 1`. Put
`r = 1 - qaryEntropy q p - 1/L` and `M = ⌊q^(r*n)⌋₊`. Then there is a code
`C : Code n α` with `M ≤ C.card` that is `(p, L)`-list-decodable — i.e. codes
of rate `r`, any rate below the capacity `1 - H_q(p)` at the cost of `1/L`,
exist for every list size `L`.

**Proof.** Preliminaries: `2 ≤ q` from `Fintype.one_lt_card`, hence `1 < (q:ℝ)`
(`natCast_one_lt_of_two_le`); `r ≤ 1` since `qaryEntropy q p > 0`
(`qary_entropy_pos`) and `1/L ≥ 0`; an auxiliary `exists_code_card_eq` builds a
code of any size `M ≤ Fintype.card (Codeword n α)`
(`Finset.exists_subset_card_eq`). Then `by_cases hML : M ≤ L`.

1. **Degenerate case `M ≤ L`.** `M ≤ q^n = Fintype.card (Codeword n α)`
   (`Fintype.card_pi`, `Nat.floor_le`, `Real.rpow_le_rpow_of_exponent_le` with
   `r * n ≤ n`). Take any `C` of size `M`; then
   `(hamming_ball ⌊p*n⌋₊ y ∩ C).card ≤ C.card = M ≤ L`
   (`Finset.card_le_card Finset.inter_subset_right`), so `list_decodable`
   holds outright — no counting needed.
2. **Main case `L < M`** (`Nat.lt_of_not_ge`). Set
   `V = ⌊q^(qaryEntropy q p * n)⌋₊`; `hV_ball` says every ball of radius
   `⌊p*n⌋₊` has at most `V` words, from
   `hamming_ball_size_asymptotic_upper_bound q n p` (radius by `mul_comm`) and
   `Nat.le_floor`. Also `hM_le : M ≤ q^n` and `hM_pos : 0 < M`.
3. `h_ineq`: the counting inequality
   `q^n · C(V,L+1) · C(q^n-(L+1), M-(L+1)) < C(q^n, M)` from
   `listDecoding_counting_ineq`, moved to `Fintype.card α` and back to ℕ by
   `exact_mod_cast` (`h_ineq_nat`).
4. `exists_listDecodable_code` with this `V`, `h_ineq_nat`, and `p ≤ 1` from
   `lt_one_of_le_one_sub_inv` returns `C` with `C.card = M` and
   `list_decodable p _ _ n L hL C`; `simp [hCcard]` gives `M ≤ C.card`. ∎

**Remark.** The conclusion says `M ≤ C.card`, not `= M`, so it reads as a rate
lower bound; the statement's two `by linarith` arguments discharge
`list_decodable`'s `0 ≤ p` and `p ≤ 1`.
