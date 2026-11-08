<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.SignQueryCheck.randomizedValue_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized Value Bounds

**Claim.** For a sign query check $C$ and a function $f$ taking values in $[-1,1]$, the randomized value of $C$ on $f$ lies in $[0,1]$.

**Proof.** The check's randomized value is the predicate's randomized value on the list of query values $f(C.queries(j))$. Each such value lies in $[-1,1]$ by the assumed bound on $f$. The predicate's randomized value lies in $[0,1]$ whenever its input means lie in that interval (`SignPredicate.randomizedValue_mem_Icc`), giving the result.

**Key facts.** `FABL.SignPredicate.randomizedValue_mem_Icc`.
