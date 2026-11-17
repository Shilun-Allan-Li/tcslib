<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.oddBLRAndAndFunctionTester_acceptanceProbability_eq_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Perfect Acceptance Characterizes Dictators

**Claim.** The uniform mixture of the odd BLR equation test and sign-AND test accepts a Boolean function with probability one exactly when it is a dictator.

**Proof.** If the mixture accepts with probability one, its acceptance probability is the average of the two component probabilities (\(\texttt{uniformMixtureFunctionTester\_acceptanceProbability}\)). Each component probability is at most one (\(\texttt{NonadaptiveFunctionTester.acceptanceProbability\_le\_one}\)); therefore both must equal one. The odd BLR component is the odd BLR acceptance probability (\(\texttt{oddBLREquationFunctionTester\_eq\_oddBLRAcceptanceProbability}\)), so its perfect acceptance characterization (\(\texttt{oddBLRAcceptanceProbability\_eq\_one\_iff\_oddParity}\)) says $f$ is parity on some odd-cardinality set $S$. For this parity, the sign-AND component accepts with probability equal to the parity-AND acceptance probability at $|S|$ (\(\texttt{signAndFunctionTester\_parity\_acceptanceProbability}\)). If $|S|\ge2$, that probability is strictly less than one (\(\texttt{parityAndAcceptanceProbability\_lt\_one\_of\_two\_le}\)), a contradiction. Oddness and positivity of $|S|$ thus force $|S|=1$, making $f$ a dictator.

Conversely, a dictator is parity on its singleton coordinate. The odd BLR characterization gives perfect acceptance by the equation test, and the sign-AND parity formula gives perfect acceptance by the other test. Their uniform average is therefore one.

**Key facts.** `FABL.uniformMixtureFunctionTester_acceptanceProbability`, `FABL.NonadaptiveFunctionTester.acceptanceProbability_le_one`, `FABL.oddBLREquationFunctionTester_eq_oddBLRAcceptanceProbability`, `FABL.oddBLRAcceptanceProbability_eq_one_iff_oddParity`, `FABL.signAndFunctionTester_parity_acceptanceProbability`, `FABL.parityAndAcceptanceProbability_lt_one_of_two_le`.
