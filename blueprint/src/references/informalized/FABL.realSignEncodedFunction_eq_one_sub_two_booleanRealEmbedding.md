<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/BentDegree.lean :: FABL.realSignEncodedFunction_eq_one_sub_two_booleanRealEmbedding -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Sign Encoding

**Claim.** For every Boolean function, its real sign encoding is the function whose value at each input is one minus twice the real embedding of the Boolean value.

**Proof.** Fix an input $x$. If $f(x)=0$, its sign encoding is $1$, while its real embedding is $0$, so both sides equal $1$. Otherwise, since the Boolean codomain has only the values $0$ and $1$, we have $f(x)=1$. Its sign encoding is then $-1$, and its real embedding is $1$, so the right side is also $1-2=-1$. Thus the two functions agree at every input.
