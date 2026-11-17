<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.b2f_eq_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding true

**Claim.** For every Boolean $a$, its encoding in $\mathrm{Fin}(2)$ equals $1$ exactly when $a$ is true.

**Proof.** Check the two Boolean values. The encoding of false is $0$, which is not $1$, while the encoding of true is $1$. Thus both sides of the equivalence hold in precisely the true case.
