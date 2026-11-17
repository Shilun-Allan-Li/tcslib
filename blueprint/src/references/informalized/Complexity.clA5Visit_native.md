<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Visit_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Computability of Stored Visits

**Claim.** If the unary string encoding the time function $t(z)$ is polynomial-time computable, then the function returning the stored visit code for tape $\tau$ at time $t(z)$ is polynomial-time computable.

**Proof.** Starting from the assumed polynomial-time unary encoding of $t(z)$, first form a unary encoding of $M.k\,t(z)$ by the multiplication closure result. The constant unary string encoding $\tau.val$ is polynomial-time computable, so the addition closure result gives a polynomial-time unary encoding of $M.k\,t(z)+\tau.val$. Separately, extracting the third header tail is polynomial-time computable. Applying the field-extraction closure result to this tail and the computed index yields the desired stored visit code; the final length and multiplication rearrangements identify that index with the one used in the definition.

**Key facts.** `Complexity.clA5Times_native`, `Complexity.clA5_pt_const`, `Complexity.clA5Add_native`, `Complexity.clHeaderTail_native`, `Complexity.clA5Field_native`.
