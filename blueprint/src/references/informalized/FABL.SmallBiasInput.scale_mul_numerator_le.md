<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.SmallBiasInput.scale_mul_numerator_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scale Numerator Bound

**Claim.** The scale and bias numerator satisfy $Sa\le nb+a$.

**Proof.** Writing the ceiling quotient as $S=\left\lfloor\frac{nb+a-1}{a}\right\rfloor$, the defining property of the floor quotient gives $Sa\le nb+a-1$. Since $nb+a-1\le nb+a$, the claimed bound follows.
