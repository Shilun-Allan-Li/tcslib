<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SATTo3SAT.lean :: SATTo3SAT.transformClause_isLocal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Locality of Encoded Clauses

**Claim.** Every 3-clause produced by encoding a clause at index $i$ has all its auxiliary variables indexed by $i$; literals over original variables are local automatically.

**Proof.** First, translating an original literal preserves its sign and replaces its variable by an original-variable marker, so each translated literal is local. Now split according to the clause length. For the empty clause, either output clause uses only the auxiliary index $i$. For clauses of length one, two, or three, the output consists of translated original literals, so locality follows from the observation above. For a longer clause, the initial output clause has two translated literals and one auxiliary literal indexed by $i$. Any other output clause belongs to the chain built from the remaining literals; the chain locality result shows that all three of its literals are local (\texttt{SATTo3SAT.buildChain\_isLocal}).

**Key facts.** `SATTo3SAT.buildChain_isLocal`.
