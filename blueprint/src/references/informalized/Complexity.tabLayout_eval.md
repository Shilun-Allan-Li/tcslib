<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauSpec.lean :: Complexity.tabLayout_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Tableau Input Layout

**Claim.** For every finite Boolean list $v$, evaluating the tab layout of length $|v|$ on input $v$, with no previously computed blocks, yields exactly $v$.

**Proof.** Both lists have length $|v|$. To compare their entries, fix an index $i<|v|$. The tab layout at that position is the input source indexed by $i$, since the layout is obtained by listing all indices from $0$ to $|v|-1$. Evaluating this source on $v$ returns the $i$th entry of $v$; the index bound ensures it is an actual entry, rather than the default value. Thus the two lists agree at every position and are equal.
