<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: chiS_flipBit -->
<!-- origin: boolean-ch02-social-choice-arrow run 352ab7ff3113 verdict not_in_text (0.68) -->

# A character under a single bit flip

**Claim.** For `S : Finset (Fin n)`, `x : BoolCube n` and a coordinate `i`,
flipping the `i`-th bit negates the character exactly when `i ∈ S`:
`chiS S (flipBit x i) = if i ∈ S then -chiS S x else chiS S x`.

**Proof.** Unfold `chiS` and `flipBit` (so the argument is
`Function.update x i (!x i)`) and split on `i ∈ S` (`by_cases hiS`).

* Case `i ∈ S`.
  1. `flipped_prod`: rewrite the product of `boolToSign` over the updated point
     as a product of an updated function (`Finset.prod_congr` plus
     `Function.update_apply` with a `split_ifs`), then peel off the `i`-th
     factor with `Finset.prod_update_of_mem hiS`, leaving
     `boolToSign (!x i) * ∏ j ∈ S \ {i}, boolToSign (x j)`.
  2. `orig_prod`: peel the same factor off the unflipped product using
     `Finset.mul_prod_erase _ _ hiS` and `Finset.erase_eq`.
  3. `hneg`: `boolToSign (!x i) = -boolToSign (x i)` by `cases x i` on the
     definition of `boolToSign`.
  4. Rewriting with the three facts and `ring` gives the negated character.
* Case `i ∉ S`. Every index `j ∈ S` satisfies `j ≠ i`, so
  `Function.update_of_ne` leaves each factor untouched; `Finset.prod_congr`
  finishes.

**Used in.** `influence_chi` (both branches) and `influence_eq_sum_fourier`,
where `f x - f (flipBit x i)` is expanded through `walsh_expansion` and this
lemma supplies the sign of each term.
