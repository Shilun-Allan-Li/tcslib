<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SATTo3SAT.lean :: SATTo3SAT.length_to3SAT_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# SAT-to-3-SAT Encoding Length Bound

**Claim.** For every CNF formula $f$, its SAT-to-3-SAT encoding has length at most the total number of literals in $f$ plus twice the number of clauses in $f$.

**Proof.** By definition, the encoding of $f$ is the recursive clause-by-clause encoding started at index $0$. Applying the recursive encoding length bound at that starting index gives the result (\texttt{SATTo3SAT.length\_to3SATAux\_le}).

**Key facts.** `SATTo3SAT.length_to3SATAux_le`.
