<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.catalog_increment_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Incrementing a run of ones

**Claim.** For every $p$ and optional list $T$, the incremented word formed from $p$ true bits and an optional false separator followed by $T$ is absent when $T$ is absent, and otherwise consists of $p$ false bits followed by true and then the list in $T$.

**Proof.** The increment rule distributes across an initial run of true bits: incrementing $p$ true bits followed by a word is the result of incrementing that word, with the $p$ leading bits changed to false (Turing.incFixed_replicate_true_append). Apply this with the word given by the optional separator followed by $T$. If $T$ is absent, that word is empty and its increment is absent, so the whole result is absent. If $T$ is present, the word begins with false and the increment rule changes that bit to true while preserving the rest of $T$. Mapping this result under the prefix of $p$ false bits gives the stated formula.

**Key facts.** `Turing.incFixed_replicate_true_append`.
