<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.pmfExpectation_comm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interchanging finite expectations

**Claim.** For independent finite probability mass functions on $\Omega$ and $\Xi$, the iterated expectation of $h(x,y)$ is unchanged when the order of the two expectations is reversed.

**Proof.** Write each expectation as its defining finite weighted sum. Distributing the outer weight through the inner sum expresses the left side as a double sum whose summand is the product of the probability weights and $h(x,y)$. Interchanging the two finite sums leaves the summand unchanged; regrouping the terms then gives the iterated expectation in the reverse order.
