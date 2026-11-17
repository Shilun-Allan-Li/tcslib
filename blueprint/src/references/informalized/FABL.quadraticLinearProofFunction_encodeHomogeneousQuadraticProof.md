<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.quadraticLinearProofFunction_encodeHomogeneousQuadraticProof -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear function from encoded proof

**Claim.** For every $w\in\mathbb{F}_2^n$, the linear function extracted from its encoded homogeneous quadratic proof has value $w\cdot x$ at every $x\in\mathbb{F}_2^n$.

**Proof.** Fix $x$. The extracted function reads the proof-table entry indexed by the encoding of $x$, then converts that Boolean entry back to an element of $\mathbb{F}_2$. In the encoded proof, the corresponding linear-table entry was defined to be precisely the encoding of $w\cdot x$. The two inverse conversions cancel, leaving $w\cdot x$. Since this holds for every $x$, the functions are equal.
