<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRead_forward -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward decoding of paired bits

**Claim.** Starting from the reader’s initial control state with stream cursor at the end of the prefix and target cursor at the end of the written prefix, after $2|w|$ steps the stream and control state are unchanged, the target becomes $\mathrm{written}\,w\,\mathrm{drop}_{|w|}(\mathrm{old})$, and the cursors advance by $2|w|$ and $|w|$, respectively.

**Proof.** Induct on the word $w$. If $w$ is empty, zero steps leave the configuration unchanged, and the claimed target and cursor expressions reduce to their initial values. For the induction step, write $w=b::w'$. The encoding begins with the pair $b,b$ followed by the encoding of $w'$. The two-step decoding fact (`clRead_pair`) says that these first two copies return the reader to its scanning state, advance the stream cursor by two and the target cursor by one, and write $b$ at the front of the target’s unread portion. The remaining stream is precisely the encoding of $w'$, with prefix extended by $[b,b]$; the target’s written prefix is extended by $[b]$, and its unread suffix is `old.tail`. Apply the induction hypothesis to this configuration. Combining the two initial steps with the $2|w'|$ subsequent steps gives the stated total time and cursor positions; the list identities yield the target $\mathrm{written}\,b::w'\,\mathrm{drop}_{|w|}(\mathrm{old})$.

**Key facts.** `Complexity.clRead_pair`, `Turing.MultiTapeTM.runFrom_add`.
