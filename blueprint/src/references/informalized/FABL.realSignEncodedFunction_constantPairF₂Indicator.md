<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SiegenthalerSharpness.lean :: FABL.realSignEncodedFunction_constantPairF₂Indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Encoding of the Constant-Pair Indicator

**Claim.** The real sign encoding of the function equal to $1$ at $0$ and the all-ones vector, and $0$ elsewhere, is $x\mapsto 1-2\mathbf{1}_{\{0,\mathbf{1}\}}(x)$.

**Proof.** Fix $x$ and split into whether $x$ is one of the two specified vectors. The membership characterization `mem_constantPairSubspace_iff` says precisely that the constant-pair subspace consists of $0$ and the all-ones vector. In the first case, the Boolean function takes value $1$, whose sign encoding has real value $-1$; the indicator is $1$, so the displayed expression is also $-1$. In the other case, the Boolean function takes value $0$, whose sign encoding has real value $1$, and the indicator is $0$, so the expression is $1$. Thus the functions agree at every $x$.

**Key facts.** `FABL.mem_constantPairSubspace_iff`.
