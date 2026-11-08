<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.gatesAcyclic_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of a list with a first gate

**Claim.** The list with first gate $g$ and remaining list $gs$ is acyclic from $n$ exactly when every input of $g$ is below $n$ and $gs$ is acyclic from $n+1$.

**Proof.** For the forward direction, apply acyclicity at position $0$ to obtain the bound $n$ for every input of $g$. At each position $i$ of $gs$, the corresponding position in the longer list is $i+1$; its input bound is $n+(i+1)=(n+1)+i$, giving acyclicity of $gs$ from $n+1$. Conversely, the position-zero condition gives the required bound for $g$. Every later position has the form $i+1$, and acyclicity of $gs$ bounds its inputs by $(n+1)+i=n+(i+1)$. These are precisely the bounds required for the concatenated list.
