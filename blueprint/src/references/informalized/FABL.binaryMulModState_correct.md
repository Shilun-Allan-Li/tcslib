<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryMulModState_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Multiplication State

**Claim.** For $\ell>0$, the encoded first component of the multiplication state after $r$ steps equals the encoding of $x$ times the encoded prefix of $y$ of length $r$; its second component equals $\alpha^r$ times the encoding of $x$, in the quotient by the associated monic polynomial.

**Proof.** Induct on the number of steps, keeping both component identities together. At zero steps, the state is $(0,x)$ and the prefix is zero, so the first identity is $0=0$; the second is the identity that the encoding of $x$ equals $\alpha^0$ times itself.

For the successor step, the first component is updated by adding the current bit of $y$ times the encoded second component to the encoded first component. The encoding rule for scale-add (`binaryAdjoinRootEncode_binaryScaleAdd`) turns this update into the same addition in the quotient. Substitute the two induction hypotheses, and expand the next prefix using `binaryAdjoinRootPrefix_succ`; the resulting expression is the encoding of $x$ times that next prefix.

The second component is updated by multiplication by $X$ modulo the defining polynomial. Its encoding is therefore multiplied by $\alpha$ (`binaryAdjoinRootEncode_binaryXMulMod`). Applying the induction hypothesis gives $\alpha(\alpha^r E(x))=\alpha^{r+1}E(x)$, proving the second identity.

**Key facts.** `FABL.binaryAdjoinRootEncode_binaryScaleAdd`, `FABL.binaryAdjoinRootPrefix_succ`, `FABL.binaryAdjoinRootEncode_binaryXMulMod`.
