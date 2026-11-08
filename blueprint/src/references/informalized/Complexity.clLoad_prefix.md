<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clLoad_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Loading a Prefix of the Row

**Claim.** For each $j\le l$, the loader reaches the configuration at field index $j$ with precisely the first $j$ fields replaced by their new words and the cursor just after their packed encodings, within time $j(2U+3W+7)$.

**Proof.** Proceed by induction on $j$. At $j=0$, zero steps leave the starting configuration unchanged; the loaded-prefix assignment is the old assignment and the encoded empty prefix has length zero. For the successor step, suppose the claimed configuration is reached at time $a$ for prefix length $j$. Set $i=j$. Decompose the packed stream at field $i$ using `clLoad_split`: the already packed prefix comes first, then the encoding of `new i` with the remaining encoded fields and trailer behind it. Apply the one-field loading lemma (`clLoad_field`) to this configuration. Its old word at $i$ is still `old i`, so its time bound is at most $2U+3W+7$; it replaces that field and advances the cursor by the length of the newly encoded field. The encoding of the first $j+1$ fields is the prior prefix followed by `pairEncode (new i) []`, whose length is $2|new i|+2$. The field update agrees with the definition of the loaded-prefix assignment after one more field (`clLoadWords_step`). Concatenating the two runs gives time $a+b\le(j+1)(2U+3W+7)$ (`runFrom_add`), and the stream split and length calculation identify the resulting configuration. The zero-step base case uses `runFrom_zero`; the remaining list identities are bookkeeping for the packed prefix.

**Key facts.** `Complexity.clFields_append`, `Complexity.clLoadWords_step`, `Complexity.clLoad_field`, `Complexity.clLoad_split`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_zero`.
