<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.bits_quasiPolyBudget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Expansion of the Budget

**Claim.** The binary expansion of the quasi-polynomial budget is the concatenation of the specified zero-output strings for successive suffixes of the seed, followed by $0,1$.

**Proof.** Put $m=\lfloor\log_2 |x|\rfloor$. The seed identity (`Randomized.budgetSeed_eq`) writes the seed as $m-1$ true bits, then a false bit, then $m$ true bits. Iteratively dropping the first bit $i$ times gives the suffix obtained by dropping $i$ bits (`Complexity.BinArith.iterate_drop_one`). On this seed, the zero-output scan of the suffix is $m$ false bits when $i<m$, and empty otherwise (`Randomized.zerosAfterZero_drop`). Thus the concatenation over the range has $m$ copies of a length-$m$ zero string, followed by the final $0,1$: the range has length at least $m$ by the bound established from the seed identity, and the count of indices below $m$ yields exactly those copies (`Randomized.flatMap_range_ite`). Finally, the binary expansion of a power of two is a string of zeros followed by one (`Turing.bits_two_pow_eq_replicate`). Since the exponent of the budget is $m^2+1$, this is precisely $m^2$ zeros followed by $1$; the stated concatenation has the same bits, using $m^2$ zeros from the scans and the appended $0,1$.

**Key facts.** `Randomized.budgetSeed_eq`, `Complexity.BinArith.iterate_drop_one`, `Randomized.zerosAfterZero_drop`, `Randomized.flatMap_range_ite`, `Turing.bits_two_pow_eq_replicate`.
