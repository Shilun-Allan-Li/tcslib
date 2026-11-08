<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitSafe_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenating Safe Computation Intervals

**Claim.** If the run from $c$ avoids the anchor state through time $u$, and the run beginning at the configuration reached after $u$ steps avoids it through time $v$, then the run from $c$ avoids it through time $u+v$.

**Proof.** Fix any time $j\le u+v$. If $j\le u$, the first safety hypothesis directly says that the run from $c$ is not in the anchor state at time $j$. Otherwise, write $j=u+(j-u)$; here $j-u\le v$. The run-from-addition identity says that the configuration reached from $c$ after $u+(j-u)$ steps is exactly the configuration reached by running for $j-u$ steps from the configuration already reached after $u$ steps (\texttt{Turing.MultiTapeTM.runFrom_add}). The second safety hypothesis therefore rules out the anchor state at time $j-u$ of that latter run, hence also at time $j$ of the original run. Since this holds for every $j\le u+v$, the full interval is safe.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
