<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/Viola.lean :: FABL.realSignEncodedFunction_add_translates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Identity for Translated Sign Encodings

**Claim.** The product of the real sign encodings of $f(x+y)$ and $f(x+y')$ equals the real sign encoding, at $x$, of the function $z\mapsto f(z+y)+f(z+y')$.

**Proof.** At the fixed point $x$, the two values on the left are the sign encodings of the bits $f(x+y)$ and $f(x+y')$. The encoding turns addition in $\mathbb F_2$ into multiplication of signs (`signEncode_add`). Applying this identity to those two bits identifies their product with the encoding of their sum. Taking real sign values preserves multiplication, which is exactly the right-hand side evaluated at $x$.

**Key facts.** `FABL.signEncode_add`.
