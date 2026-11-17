<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SiegenthalerSharpness.lean :: FABL.booleanFunctionF₂Encoding_booleanFunctionF₂Decoding -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding After Decoding

**Claim.** For every binary Boolean function $f$, encoding its decoding recovers $f$ exactly.

**Proof.** Fix a binary input $x$. Encoding the decoded function evaluates it at the sign vector corresponding to $x$. Decoding there evaluates $f$ at the binary vector obtained by transporting that sign vector back, which is $x$ by the inverse equivalence. The output is therefore the sign encoding of $f(x)$; applying the inverse binary-sign equivalence recovers $f(x)$. Since the two functions agree at every input, they are equal.
