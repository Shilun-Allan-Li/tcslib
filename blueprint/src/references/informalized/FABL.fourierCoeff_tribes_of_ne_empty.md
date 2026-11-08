<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.fourierCoeff_tribes_of_ne_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tribes Fourier coefficient

**Claim.** For nonempty $T$, the Fourier coefficient of the tribes function is $2(-1)^{k+|T|}2^{-kw}(1-2^{-w})^{s-k}$, where $k$ is the number of tribes meeting $T$.

**Proof.** The product formula for the tribes Fourier coefficient expresses it as $2\cdot 2^{-s}$ times a product of one expectation for each tribe; the empty-set correction vanishes because $T\ne\varnothing$ (the product formula, `FABL.fourierCoeff_tribes_eq_prod`). The product of these expectations is $2^s(1-2^{-w})^{s-k}(2^{-w})^k(-1)^{|T|+k}$ (`FABL.prod_expect_one_add_and_tribeFrequencyPart`). Set $k$ equal to the support size. The factors $2^{-s}$ and $2^s$ cancel, and $(2^{-w})^k=2^{-kw}$. Reordering the factors gives the stated expression.

**Key facts.** `FABL.fourierCoeff_tribes_eq_prod`, `FABL.prod_expect_one_add_and_tribeFrequencyPart`.
