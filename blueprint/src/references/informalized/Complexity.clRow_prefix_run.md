<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRow_prefix_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Prefix Construction

**Claim.** For every $j\le l$, the row controller reaches field $j$ in copier start control within $j(3W+4)$ steps, with the input position, counter-tape contents, and head positions unchanged, and with the record extended by the stored prefix of the first $j$ counter words.

**Proof.** Induct on $j$. For $j=0$, time zero gives the initial configuration, and the stored prefix is empty. For the successor case, suppose the machine reaches field $j$ with the first $j$ encodings recorded at time $t\le j(3W+4)$. Apply the one-field copying result (`clRow_field`) to field $j$ and this current record. It supplies a time $s\le 3|w(j)|+4\le 3W+4$ to reach field $j+1$ and append that field’s encoding. The run-composition law (`runFrom_add`) lets us concatenate these two runs, giving time $t+s$. The time bound follows by addition, and the recursive definition of the stored prefix, together with associativity of list concatenation, identifies the resulting record as the prefix through field $j$.

**Key facts.** `Complexity.clRow_field`, `Turing.MultiTapeTM.runFrom_add`.
