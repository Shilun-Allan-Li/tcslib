<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satChain_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of the Clause-Splitting Chain

**Claim.** If the CNF formula produced by the clause-splitting chain from head $h$, remainder $R$, and cursor $n$ is satisfied by $a$, then the clause $h::R$ is satisfied by $a$.

**Proof.** Induct on the remainder, generalizing the head and cursor. When the remainder has fewer than three literals, the chain consists of the single clause $h::R$, so the conclusion is exactly the assumed satisfaction. Otherwise the chain begins with the link clause $[h,b,(n,\mathrm{true})]$ and continues with the chain for head $(n,\mathrm{false})$, tail $c::d::\ldots$, and cursor $n+1$. Satisfaction of the whole CNF gives satisfaction of the link clause and of that recursive chain. By induction, the recursive chain implies that the continuation clause $[(n,\mathrm{false}),c,d,\ldots]$ is satisfied. If $a(n)$ is false, the positive literal for $n$ in the link clause is false, so the link clause forces $h$ or $b$ to be true. If $a(n)$ is true, the negative literal in the continuation is false, so the continuation forces some literal in $c::d::\ldots$ to be true. In both cases at least one literal in $h::b::c::d::\ldots$ is true, proving the original clause is satisfied.
