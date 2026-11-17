<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satDrop_parse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parsing the Doubled Prefix

**Claim.** For any decomposition $u=p\mathbin{++}r$, starting at offset $2|p|$ with a unary counter of length and head position $|p|$ and empty output, the machine processes the doubled encoding of $r$ in $2|r|$ steps and finishes at offset $2|u|$ with counter length and head position $|u|$ and empty output.

**Proof.** Proceed by induction on the suffix $r$. If $r$ is empty, then $u=p$, so the starting and claimed configurations coincide, and zero steps leave the configuration unchanged (`runFrom_zero`). Now write $r=b::r'$. The pair encoding splits as the doubled encoding of $p$, followed by the two copies $b,b$, then the doubled encoding of $r'$ and the separator and second word. The length law for the doubled encoding (`satBits_length`) gives this decomposition in the required positions. By the doubled-bit result (`satDrop_double`), the first two steps consume the pair $b,b$, advance the offset by two, and extend the counter from length and head position $|p|$ to $|p|+1$. The remaining $2|r'|$ steps are then handled by the induction hypothesis applied to the longer prefix $p\mathbin{++}[b]$ and suffix $r'$. Splitting the total run into these two consecutive portions is justified by the run concatenation law (`runFrom_add`); the list-length arithmetic identifies the resulting endpoint with the one asserted for $u$.

**Key facts.** `Complexity.satBits_length`, `Complexity.satDrop_double`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_zero`.
