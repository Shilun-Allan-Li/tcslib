<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.majority_odd_isNonconstant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonconstancy of Odd Majority

**Claim.** For every natural number $m$, the majority function on $\{-1,1\}^{2m+1}$ is nonconstant.

**Proof.** Take the two constant inputs, one equal to $-1$ in every coordinate and the other equal to $1$ in every coordinate. Since $2m+1$ is positive, the unanimous-input property of majority (\texttt{majority\_unanimous}) says that majority takes the corresponding unanimous values on these inputs. Those two outputs are distinct, so majority is nonconstant.

**Key facts.** `FABL.majority_unanimous`.
