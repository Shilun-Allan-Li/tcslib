<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.configurationValidity_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of Valid Configuration Codes

**Claim.** Under the stated lower bound on $C$, a word of length $C(s+n+1)$ satisfies the configuration-validity formula exactly when it is the code of an in-window configuration on a Boolean input of length $n$.

**Proof.** The formula is the conjunction of the relabeled core validity constraints and padding clauses. By the characterization of core validity (`codecValidity_eval`), satisfaction of the first part gives a codec row $r$ whose bits are precisely the assigned bits. The padding clauses say that every assigned bit from the row-code range up to the word length is false (`codecPadding_eval`). Realize $r$ as an input $x$ of length $n$ and an in-window configuration $c$, with the resulting row equal to $r$ (`codecRow_realize`). The lower bound on $C$ makes the row-bit alphabet fit into the code length (`codecBit_card_le`); the padding condition and word length then let the code be reconstructed from its row bits (`codecWord_reconstruct`). Hence the word is the configuration code of $c$. Conversely, suppose the word is such a configuration code. Take the row obtained from $x$ and $c$. At every row-bit position, the code returns the corresponding bit (`codecWord_get`), so its bits agree with that row. At every position beyond the row-bit range the code is false (`codecWord_padding`), satisfying all padding clauses. The row validity characterization and the padding characterization therefore give satisfaction of the whole formula.

**Key facts.** `Complexity.codecValidity_eval`, `Complexity.codecPadding_eval`, `Complexity.codecRow_realize`, `Complexity.codecBit_card_le`, `Complexity.codecWord_reconstruct`, `Complexity.codecWord_get`, `Complexity.codecWord_padding`.
