<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.binaryAdjoinRootEncode_executableSmallBiasPowerSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the power-sum polynomial

**Claim.** Encoding the modular vector sum of the scaled powers $r^{i+1}$ equals the value at the encoding of $r$ of the polynomial whose terms are $\gamma_i X^{i+1}$.

**Proof.** First express evaluation of the polynomial as the sum of its coefficient scalars times powers of the evaluation point (`executableSmallBiasPolynomial_eval`). The encoding map is linear, so it carries the finite sum defining the modular power sum to the sum of the encodings of its terms, and it carries scalar multiplication by $\gamma_i$ to multiplication by the corresponding scalar in the quotient algebra. For each index $i$, encoding the modular power $r^{i+1}$ equals the $(i+1)$st power of the encoding of $r$ (`binaryAdjoinRootEncode_binaryPowMod`). Substituting these termwise equalities gives exactly the polynomial evaluation sum.

**Key facts.** `FABL.executableSmallBiasPolynomial_eval`, `FABL.binaryAdjoinRootEncode_binaryPowMod`.
