<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KhintchineKahane.lean :: FABL.rademacherNorm_even -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evenness of the Rademacher norm

**Claim.** For every sign vector $x$, the norm of the signed sum at $-x$ equals its norm at $x$.

**Proof.** For each coordinate, changing $x_i$ to $-x_i$ changes its real sign value to the negative of its former value. Therefore the entire signed sum at $-x$ is the negative of the signed sum at $x$, by linearity of scalar multiplication and finite summation. A norm is unchanged by negation, so the two norms agree.
