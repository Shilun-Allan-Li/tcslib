<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clSearchArg_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Native Query Arguments

**Claim.** If the input-dependent word $y(x)$ and unary word of length $T(x)$ are polynomial-time computable, then the packed query argument formed from the machine, $y(x)$, $T(x)$, and the selected coordinates is polynomial-time computable.

**Proof.** List the $l+5$ component words used to form the query argument, where $l$ is the number of movement-count fields. The first component is constant, as is the final empty component; each is polynomial-time computable by constant-function computability and the fact that a linear time bound is polynomial. The stream of recorded configurations is polynomial-time computable by the trajectory-computability result (`Complexity.clTrajectory_native`). The two target words are the binary encodings of the final counts at the selected coordinates, and each is polynomial-time computable by the final-count result (`Complexity.clFinalCount_native`). The remaining component is the unary word of length $T(x)$, computable by hypothesis. Thus every component in the list is polynomial-time computable. The closure of polynomial-time computability under packing a finite list of component words (`Complexity.clNative_fields`) then gives the result.

**Key facts.** `Turing.FinTM.computesFunInTime_const`, `Complexity.clNative_linear`, `Complexity.clTrajectory_native`, `Complexity.clFinalCount_native`, `Complexity.clNative_fields`.
