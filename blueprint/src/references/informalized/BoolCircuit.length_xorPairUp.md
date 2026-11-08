<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.length_xorPairUp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length after pairing circuit pairs

**Claim.** Pairing consecutive entries of $ps$ by the specified operation, retaining a final unpaired entry when present, produces a list of length $\left\lfloor\frac{|ps|+1}{2}\right\rfloor$.

**Proof.** Proceed by the defining cases of the pairing operation. For an empty list, both sides are zero; for a singleton, both sides are one. If the list begins with two entries and has tail $ps'$, the operation produces one entry followed by the result of pairing $ps'$. By induction, that result has length $(|ps'|+1)/2$, so the total is $1+(|ps'|+1)/2$. Since the original list has length $|ps'|+2$, elementary arithmetic on natural-number division by two identifies this total with $(|ps'|+3)/2$, as required.
