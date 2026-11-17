<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RandomFunctions.lean :: FABL.pBiasedRandomFunctionPMF_toMeasure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product law for biased random functions

**Claim.** For $p\in[0,1]$, the measure associated with the product probability law on Boolean-valued functions on $\{-1,1\}^n$, with independent values each true with probability $p$, is the product measure of the corresponding single-bit laws.

**Proof.** Apply the product-to-measure identity for independent finite-coordinate probability laws: the measure associated with the independent product PMF is the product of the measures of its coordinate PMFs (\texttt{independentProductPMF\_toMeasure}). The random-function PMF is exactly this independent product, with every coordinate law equal to the $p$-biased bit PMF. Substituting that family into the identity gives the claimed equality.

**Key facts.** `FABL.independentProductPMF_toMeasure`.
