<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.boolAndFunctionTester_parity_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity tester acceptance probability

**Claim.** For every $n\ge 0$ and every subset $S\subseteq\{0,\ldots,n-1\}$, the Boolean AND tester accepts the parity function indexed by $S$ with probability $\frac12+\left(\frac34-\frac14(-1)^{|S|}\right)2^{-|S|}$.

**Proof.** The Boolean tester's acceptance probability is the average, over independent uniform Boolean strings $x,y$, of the indicator that $f(x)\wedge f(y)=f(x\wedge y)$ (\(\texttt{FABL.boolAndFunctionTester_acceptanceProbability}\)). Reindex both uniform averages through the bijection from Boolean strings to sign strings. This bijection preserves coordinatewise AND as sign-cube AND and preserves Boolean AND on outputs as sign AND (\(\texttt{FABL.pcppBoolCubeSignEquiv_boolCubeAnd}\), \(\texttt{FABL.pcppBoolSignEquiv_boolAnd}\)). Thus the average becomes exactly the sign tester's acceptance probability on the sign parity function. The sign tester's parity formula gives the stated expression, completing the equality (\(\texttt{FABL.signAndFunctionTester_acceptanceProbability}\), \(\texttt{FABL.signAndFunctionTester_parity_acceptanceProbability}\)).

**Key facts.** `FABL.boolAndFunctionTester_acceptanceProbability`, `FABL.pcppBoolCubeSignEquiv_boolCubeAnd`, `FABL.pcppBoolSignEquiv_boolAnd`, `FABL.signAndFunctionTester_acceptanceProbability`, `FABL.signAndFunctionTester_parity_acceptanceProbability`.
