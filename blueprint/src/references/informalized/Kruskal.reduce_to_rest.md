<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Exchange.lean :: Kruskal.reduce_to_rest -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Removing a redundant candidate edge

**Claim.** If the edges in $S$ all occur in $e :: \mathit{rest}$, merging $S$ induces the same partition as merging $\mathit{rest}$, and $e$ is already redundant for $\mathit{uf}$, then some sublist of $S$ consisting only of edges from $\mathit{rest}$ still induces the partition of $\mathit{rest}$ and has no greater total weight than $S$.

**Proof.** Take $S'$ to be the sublist of $S$ obtained by retaining exactly those edges that occur in $\mathit{rest}$. First, merging $S'$ gives the same partition as merging all of $S$. To see this, induct on $S$, allowing the current union-find state to vary. If its head edge $x$ belongs to $\mathit{rest}$, retain it and apply the induction hypothesis after merging its endpoints. If $x$ does not belong to $\mathit{rest}$, the support hypothesis forces $x=e$; since $e$ is redundant in the current state, merging it changes nothing, so it can be discarded and the induction hypothesis applies to the unchanged state. Thus filtering out edges absent from $\mathit{rest}$ preserves the partition. By transitivity of equality of induced partitions (\texttt{UF.SamePartition.trans}), and the assumed partition equality for $S$ and $\mathit{rest}$, $S'$ induces the partition of $\mathit{rest}$. Every retained edge belongs to $\mathit{rest}$ by construction. Finally, filtering a list cannot increase the sum of its nonnegative edge weights: an induction on the list either keeps the head weight on both sides or removes that nonnegative contribution. Hence the total weight of $S'$ is at most that of $S$.

**Key facts.** `Kruskal.UF.SamePartition.rfl`, `Kruskal.merge_noop`, `Kruskal.UF.SamePartition.trans`.
