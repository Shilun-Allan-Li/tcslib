<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumAny_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of Consecutive Rank Testing

**Claim.** The test over the $\mathrm{count}$ consecutive ranks beginning at $i$ returns true exactly when some $j$ satisfies $i\le j<i+\mathrm{count}$ and $a(j)=\mathrm{true}$.

**Proof.** Induct on $\mathrm{count}$, with the starting rank arbitrary. For zero tests, the procedure returns false and the interval contains no possible witness. For one more test, first consider whether $a(i)$ is true. If so, $i$ itself witnesses the stated interval condition. If not, the procedure continues with the remaining tests starting at $i+1$. The induction hypothesis describes exactly when one of those later ranks succeeds; translating its interval endpoints gives $i+1\le j<i+1+\mathrm{count}$. Conversely, a witness in the full interval cannot be $i$, because $a(i)$ is false, so it lies in that later interval and the induction hypothesis makes the recursive test true.
