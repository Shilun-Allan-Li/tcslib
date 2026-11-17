<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.mem_stack_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stack Address Characterization

**Claim.** For natural numbers $q,Q$ and integer $a$, $a$ belongs to the set of stack addresses $c(j)=-2j$ with $q\le j<Q$ if and only if $c(Q)<a\le c(q)$ and $2$ divides $a$.

**Proof.** Membership says that $a=-2j$ for an integer index $j$ with $q\le j<Q$. These index bounds give $-2Q<a\le -2q$, and the address is divisible by $2$. Conversely, if those inequalities hold and $a$ is divisible by $2$, set $j=(-a/2)^{\mathrm{nat}}$. The inequalities give $q\le j<Q$, and divisibility gives $a=-2j$, so $a$ is one of the specified stack addresses.

**Key facts.** `Set.mem_ofPred_eq`.
