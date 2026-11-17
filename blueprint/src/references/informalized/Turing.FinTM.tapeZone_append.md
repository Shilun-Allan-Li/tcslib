<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.tapeZone_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Splitting a zone

**Claim.** The zone of $n+m$ blocks starting at $j$ is the concatenation of the zone of $n$ blocks starting at $j$ and the zone of $m$ blocks starting at $j+n$.

**Proof.** Induct on $n$, allowing the starting coordinate $j$ to vary. If $n=0$, the first zone is empty, so the identity follows from the definition. For the successor step, expand the first block at $j$ and apply the induction hypothesis to the remaining $n+m$ blocks starting at $j+1$. Associativity of concatenation groups the first $n+1$ blocks together; the remaining zone starts at $j+1+n=j+(n+1)$, as required.
