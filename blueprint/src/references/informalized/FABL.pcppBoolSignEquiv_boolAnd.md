<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.pcppBoolSignEquiv_boolAnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Encoding Preserves Conjunction

**Claim.** For Booleans $a$ and $b$, the sign encoding of $a\land b$ is $-1$ exactly when both encoded signs are $-1$, and is $1$ otherwise.

**Proof.** Check the four pairs. If both inputs are true, their conjunction is true, whose sign is $-1$; both encoded signs are then $-1$, so `signAnd` also gives $-1$. If either input is false, the conjunction is false and its sign is $1$; at least one encoded sign is $1$, so the condition defining `signAnd` fails and it gives $1$.
