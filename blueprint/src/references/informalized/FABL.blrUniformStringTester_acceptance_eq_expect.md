<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPTesterExamples.lean :: FABL.blrUniformStringTester_acceptance_eq_expect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform String Tester Acceptance

**Claim.** The BLR uniform string tester's acceptance is the iterated uniform expectation of the indicator that $f(x)+f(y)=f(x+y)$.

**Proof.** A seed is a uniformly chosen pair $(x,y)$, and the tester's acceptance is the expectation of the indicator that the associated CSP predicate accepts the assignment. Rewriting the uniform expectation on the product seed space as an iterated expectation, it remains to identify the predicate evaluated on the queried values. The evaluation identity for the BLR CSP predicate (`blrCSPPredicate_eval`) says this is exactly the decision of the BLR equation $f(x)+f(y)=f(x+y)$. Therefore the seedwise indicators agree, and so do their iterated expectations.

**Key facts.** `FABL.blrCSPPredicate_eval`.
