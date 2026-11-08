<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadLimitations.lean :: FABL.e3LinCheckSignedValue_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper bound for signed acceptance value

**Claim.** For every sign-query check and Boolean function, the signed value, twice the randomized acceptance value minus one, is at most $1$.

**Proof.** The randomized acceptance value lies in $[0,1]$ (`FABL.SignQueryCheck.randomizedValue_mem_Icc`). In particular it is at most $1$. Therefore twice that value minus one is at most $2\cdot1-1=1$, which is the desired bound.

**Key facts.** `FABL.SignQueryCheck.randomizedValue_mem_Icc`.
