<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/ViolaAuxiliary.lean :: FABL.multiplicativeDerivative_realSignEncodedFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a Sign Encoding

**Claim.** For a Boolean function on the Boolean cube, the product of the real sign encodings at $x+y$ and $x$ equals the real sign encoding of its Boolean derivative at $x$.

**Proof.** Write the real sign encoding at a point as the real value of the group sign encoding. The sign encoding converts addition in $\mathbb{F}_2$ into multiplication of signs (`FABL.signEncode_add`). Apply this identity to the two values $f(x)$ and $f(x+y)$. Since multiplication of signs is commutative, their product is the sign encoding of $f(x)+f(x+y)$, which is the Boolean derivative at $x$. Taking real values gives the claimed equality.

**Key facts.** `FABL.signEncode_add`.
