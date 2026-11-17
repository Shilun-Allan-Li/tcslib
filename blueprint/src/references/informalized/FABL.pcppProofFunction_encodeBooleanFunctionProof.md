<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.pcppProofFunction_encodeBooleanFunctionProof -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding and Decoding Boolean Functions

**Claim.** For every natural number $N$ and every function $f:\{-1,1\}^N\to\{-1,1\}$, encoding its values as Booleans indexed by the $2^N$ points of the sign cube and then decoding that Boolean function on the sign cube recovers $f$.

**Proof.** Fix an input $x$ in the sign cube. The encoding first indexes $x$ by its corresponding element of $\mathrm{Fin}(2^N)$, then converts $f(x)$ to a Boolean using the inverse of the Boolean-to-sign equivalence. Decoding uses the same index and converts that Boolean back to a sign. Since an equivalence followed by its inverse is the identity, the decoded value at $x$ is $f(x)$. This holds at every input, so the functions agree.
