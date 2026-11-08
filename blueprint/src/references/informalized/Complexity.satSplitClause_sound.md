<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satSplitClause_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of Clause Splitting

**Claim.** For a clause $C$, if every clause produced by splitting $C$ at cursor $n$ is satisfied by an assignment $a$, then $C$ is satisfied by $a$.

**Proof.** If $C$ is empty, its split formula is the singleton formula containing the empty clause; the assumed satisfaction of that formula directly gives the required evaluation of $C$. If $C$ has a head literal, splitting is the chain construction applied to that head and the remaining clause. The chain soundness result ($\texttt{satChain_sound}$) says that satisfaction of the resulting formula implies satisfaction of the original head followed by the remaining literals, which is exactly $C$.

**Key facts.** `Complexity.satChain_sound`.

**Caveat.** The informal payload describes a broader width-reduction theorem, but the supplied formal statement and proof establish only this soundness implication.
