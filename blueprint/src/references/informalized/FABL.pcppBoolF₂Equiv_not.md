<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.pcppBoolF₂Equiv_not -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negation in the Binary Field

**Claim.** For every Boolean $b$, the image of its negation in $\mathbb F_2$ is the image of $b$ plus $1$.

**Proof.** Check the two Boolean values. If $b$ is false, its negation is true, whose image is $1$; the image of false is $0$, so the right side is also $0+1=1$. If $b$ is true, its negation is false, whose image is $0$; the right side is $1+1=0$ in $\mathbb F_2$, since $2=0$ there.
