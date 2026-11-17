<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: Language.le_allOnes_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Languages Contained in the All-Ones Language

**Claim.** A Boolean language is contained in the all-ones language exactly when each of its words is a list of true bits of some length.

**Proof.** If $L$ is contained in the all-ones language and $w\in L$, then $w$ belongs to that language. By `Language.mem_allOnes_iff`, this means $w$ equals the list consisting of $|w|$ true bits. Conversely, suppose every $w\in L$ is a list of $n$ true bits for some $n$. Every entry of such a list is true, so each $w$ belongs to the all-ones language. This proves the containment.

**Key facts.** `Language.mem_allOnes_iff`.
