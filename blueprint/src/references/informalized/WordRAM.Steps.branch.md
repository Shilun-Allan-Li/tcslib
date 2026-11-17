<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.Steps.branch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Branching and Step Sequences

**Claim.** If $n$ steps end at program counter $l$ when $v<0$ and at $\mathrm{pos}$ otherwise, and $p$ is equivalent to $v\ge 0$, then under $\mathrm{pos}=\mathrm{pos}'$, $p$ implies that the steps end at $\mathrm{pos}'$, while $\neg p$ implies that they end at $l$.

**Proof.** Replace $\mathrm{pos}'$ by $\mathrm{pos}$ using their equality. Split on whether $p$ holds. If it does, the equivalence $p\leftrightarrow\neg(v<0)$ shows that $v<0$ is false; the conditional final program counter is therefore $\mathrm{pos}$, and the given step sequence has the required endpoint. If $p$ fails, then $\neg p$ and the reverse implication in the equivalence show that $v<0$ cannot be false; hence $v<0$. The conditional endpoint is then $l$, as required. The two implications whose antecedents contradict the selected case hold vacuously.
