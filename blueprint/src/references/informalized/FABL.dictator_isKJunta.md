<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.dictator_isKJunta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Dictator Is a One-Junta

**Claim.** For any coordinate $i$ in dimension $n$, the function that returns the sign at coordinate $i$ is a $1$-junta.

**Proof.** Choose the singleton set $S=\{i\}$. It has cardinality one, hence at most one. If two inputs agree on every coordinate in $S$, then in particular they agree at $i$; the dictator outputs their values at that coordinate, so the outputs agree. Thus the dictator depends only on a set of at most one coordinate.
