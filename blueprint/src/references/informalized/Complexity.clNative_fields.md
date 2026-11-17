<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clNative_fields -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Packing of Function Values

**Claim.** If every function in a finite list of binary-word functions is polynomial-time computable, then the function mapping an input to the packed encoding of their values in list order is polynomial-time computable.

**Proof.** Induct on the list of functions. For the empty list, the packed output is the constant empty word, which is computable in linear time (`Turing.FinTM.computesFunInTime_const`) and hence polynomial time (`Complexity.clNative_linear`). For a nonempty list with head $f$ and tail $fs$, the head value $f(x)$ is polynomial-time computable by hypothesis. The induction hypothesis says the packed encoding of the tail values is polynomial-time computable, since every function in the tail still satisfies the assumed condition. Pair these two outputs with the polynomial-time pairing construction (`Complexity.clNative_pair`). By the recursive definition of the packed encoding, this pair is exactly the encoding of the values for the whole list.

**Key facts.** `Turing.FinTM.computesFunInTime_const`, `Complexity.clNative_linear`, `Complexity.clNative_pair`.
