<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_select_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the Selected Word

**Claim.** For equal-length Boolean words $mask$ and $w$, the length of the word selected from $w$ along $mask$ equals the number of true entries of $mask$.

**Proof.** Induct on $mask$, generalizing over $w$. If $mask$ is empty, the selection is empty, and the filtered mask is empty as well. Otherwise write $mask=emit::mask'$. Equality of lengths forces $w=b::w'$; the tails have equal length. If $emit$ is false, selection discards $b$, and filtering discards $emit$, so the induction hypothesis gives the equality. If $emit$ is true, selection contributes the one-bit word $[b]$, while filtering contributes one true entry. In both cases the corresponding lengths increase by the same amount, and the induction hypothesis handles the tails.
