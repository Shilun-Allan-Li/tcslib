<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.exists_FinNDTM_maskSelect_of_eff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Efficient Masked Selection

**Claim.** For an efficient verifier M and natural numbers a,k, there are polynomial bounds and a finite nondeterministic machine that, on every choice word of the bounded length, halts and outputs M applied to a mask-selected word of the prescribed length; the mask has exactly the prescribed number of true entries and fits within the choice word.

**Proof.** Represent the pair (x,u) as one string by splitting an input according to its length. The split-solving procedure has a polynomial-time implementation (`Turing.FinTM.computesFunInTime_splitSolve`). When u has length polyLen(a,k,|x|), the defining identity for solveSplit ensures that applying this procedure to x appended to u recovers the encoded pair (x,u) (`Complexity.Meyer.solveSplit_self'`).

The verifier's accepting language V₁ is in P by the efficiency assumption. Taking its preimage under the split-and-encode procedure gives another language in P, since polynomial-time computability is preserved under preimages (`Complexity.preimage_mem_P`). The split identity shows that, on x appended to a correctly sized u, this language's indicator equals M(x,u).

Apply the mask-selection host construction to this preimage language. It supplies K,e, a machine N, and for each x an offset s and mask. The mask's number of true entries is polyLen(a,k,|x|), and s plus its full length fits in K(|x|^e+1). The host machine halts on every choice word of that length and outputs the indicator of the preimage language on x appended to the selected word. The selected segment has length equal to the mask's length, so the length formula for masked selection identifies its output length with the number of true mask entries (`Randomized.length_maskSelect`). The preimage-indicator identity then turns the host output into the singleton containing M applied to that selected word, which proves the asserted output and length properties.

**Key facts.** `Turing.FinTM.computesFunInTime_splitSolve`, `Complexity.Meyer.solveSplit_self'`, `Complexity.preimage_mem_P`, `Complexity.exists_maskSelect_host`, `Randomized.length_maskSelect`.
