<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5WorkFragment_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Computability of Work Fragments

**Claim.** If the unary encoding of $t(z)$ is polynomial-time computable, then the work fragment for tape $\tau$ at time $t(z)$ is polynomial-time computable.

**Proof.** The stored-visit computability result gives a polynomial-time stored visit code at time $t(z)$. Extracting its tail is polynomial-time computable, and the capped numeric decoding remains polynomial-time computable when supplied with the polynomial-time unary horizon bound from the stored-size result. The input size and time are likewise polynomial-time computable in unary. The two possible clause groups, for no previous visit and for a previous visit, are polynomial-time computable by the group result, using respectively the constant zero source index and the decoded, capped source index. Finally, the equality test for whether the visit code is empty is polynomial-time computable, so conditional closure combines these two cases into the desired work-fragment function.

**Key facts.** `Complexity.clA5Visit_native`, `Complexity.clHeaderTail_native`, `Complexity.clA5Sizes_native`, `Complexity.clA5SmallNum_native`, `Complexity.clA5Group_native`, `Complexity.clA5_pt_eq`, `Complexity.clA5_pt_cond`.
