<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Generator.lean :: BooleanAnalysis.GaussianSpace.exp_neg_mem_correlationInterval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative exponential lies in the correlation interval

**Claim.** For every $t\ge0$, the real number $e^{-t}$ belongs to $[-1,1]$.

**Proof.** The exponential is strictly positive, so $e^{-t}>0$ and hence $-1\le e^{-t}$. Also, $-t\le0$ because $t\ge0$; the exponential is at most $1$ on nonpositive inputs. Together these inequalities place $e^{-t}$ in $[-1,1]$.
