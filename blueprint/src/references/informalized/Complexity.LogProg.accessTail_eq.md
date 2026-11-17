<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.accessTail_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tail Comparison Formula

**Claim.** The tail comparison returns no value when the last bit of $w_i$, if present, or otherwise the supplied remembered bit $a$, is false; in every other case it returns $e$ conjoined with the assertion that $w_r=w_i$.

**Proof.** Induct on $w_i$, generalizing the comparison word $w_r$, the Boolean accumulator $e$, and the remembered bit $a$. When $w_i$ is empty, the operation tests the remembered bit: a remembered false bit yields no value, while any other case yields $e$ conjoined with the assertion that $w_r$ is empty. This is the claimed formula for the empty word. For $w_i=b::w_i'$, one step compares the heads, updates the accumulator by requiring the head of $w_r$ to equal $b$, and recurses on the two tails while remembering $b$. The induction hypothesis gives the result for the tails. Splitting on whether each tail is empty resolves the last-bit condition: if $w_i'$ is nonempty its final bit determines the outcome; if it is empty, the newly remembered bit $b$ does. The head comparison together with equality of tails is precisely equality of the original words, yielding the formula.
