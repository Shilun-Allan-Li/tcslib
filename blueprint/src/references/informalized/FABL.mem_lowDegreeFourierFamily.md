<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.mem_lowDegreeFourierFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-degree Fourier family membership

**Claim.** A set $S$ belongs to the family of coordinate subsets of size at most $k$ exactly when $|S|\le k$.

**Proof.** The family is the union, over integers $j$ from $0$ through $k$, of the families of subsets having cardinality exactly $j$. Thus membership means that $S$ has cardinality equal to some such $j$, which is equivalent to $|S|\le k$.
