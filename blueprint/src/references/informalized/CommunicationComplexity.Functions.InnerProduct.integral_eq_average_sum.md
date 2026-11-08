<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.integral_eq_average_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integral as a finite average

**Claim.** For any real-valued function on the $n$-bit Boolean inputs, its integral against the uniform probability measure equals $2^{-n}$ times the sum of its values over all inputs.

**Proof.** The integral over a finite probability space is the sum of the function values weighted by their point masses (\texttt{FiniteProbabilitySpace.integral\_eq\_pmf\_sum}). Each Boolean input has mass $2^{-n}$ (\texttt{pmf\_toReal\_eq\_two\_pow\_inv}). Substituting this common weight into the finite sum and factoring it out gives the stated average.

**Key facts.** `CommunicationComplexity.FiniteProbabilitySpace.integral_eq_pmf_sum`, `CommunicationComplexity.Functions.InnerProduct.pmf_toReal_eq_two_pow_inv`.
