<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5InputFragment_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Input-Fragment Production

**Claim.** For a finite Boolean Turing machine with a binary code for its optional states, if the unary encoding of the time function is polynomial-time computable, then the input fragment at that time is polynomial-time computable.

**Proof.** First, the stored input-head position at the requested time has a polynomial-time computable unary encoding (`clA5InputPos_native`). The input fragment chooses between two clause groups according to whether this position lies between $1$ and the stored input size. Both bounds have polynomial-time computable unary encodings: the lower bound is constant, and the upper bound is supplied by the input-size estimate (`clA5Sizes_native`). Comparing unary values and combining the two comparisons gives a polynomial-time computable one-bit test (`clA5Le_native`, `clA5_pt_and`). For the in-range branch, the group parameters are polynomial-time computable: the input size and time are available, the position argument is obtained by subtracting one, and the source offset is constant (`clA5Sub_native`, `clA5_pt_const`). The group-production result then gives a polynomial-time machine for that fragment (`clA5Group_native`). For the out-of-range branch, use the same group-production result with the constant absent-symbol parameters. Finally, selecting the in-range or out-of-range output according to the test preserves polynomial-time computability (`clA5_pt_cond`), and this conditional is exactly the defined input-fragment construction.

**Key facts.** `Complexity.clA5InputPos_native`, `Complexity.clA5Sizes_native`, `Complexity.clA5Le_native`, `Complexity.clA5_pt_and`, `Complexity.clA5Sub_native`, `Complexity.clA5Group_native`, `Complexity.clA5_pt_const`, `Complexity.clA5_pt_cond`.
