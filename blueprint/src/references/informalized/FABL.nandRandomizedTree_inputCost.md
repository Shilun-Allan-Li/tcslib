<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.nandRandomizedTree_inputCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected input cost of the randomized tree

**Claim.** For each two-coordinate input $x$, the expected number of queried coordinates is $\bigl(c(x_0)+c(x_1)\bigr)/2$, where $c(1)=1$ and $c(-1)=2$.

**Proof.** The random seed is uniform on two choices, selecting either the tree that queries coordinate $0$ first or the tree that queries coordinate $1$ first. The uniform-seed expectation identity converts the expected cost into the average of these two query counts (\texttt{FABL.pmfExpectation_uniformPMF_eq_expect}). The first tree's query count is $1$ when $x_0=1$ and $2$ otherwise (\texttt{FABL.nandTree01_queryCount}); the second's is $1$ when $x_1=1$ and $2$ otherwise (\texttt{FABL.nandTree10_queryCount}). Averaging these costs gives the claimed formula.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.nandTree01_queryCount`, `FABL.nandTree10_queryCount`.
