<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.pmf_toReal_eq_two_pow_inv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform mass of Boolean inputs

**Claim.** For the uniform probability measure on the $n$-bit Boolean inputs, every input has mass $1/2^n$.

**Proof.** The point mass in the probability mass function is the measure of the singleton containing the input. For the uniform measure on the whole space, this is the counting measure of that singleton divided by the cardinality of the space. The singleton has counting measure $1$, and the space of functions from an $n$-element set to a two-element set has cardinality $2^n$. Hence the mass is $1/2^n$.
