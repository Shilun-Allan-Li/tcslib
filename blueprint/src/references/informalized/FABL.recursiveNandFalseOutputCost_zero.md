<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNandFalseOutputCost_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial False-Output Cost

**Claim.** At level $0$, the maximum expected query cost among inputs on which the recursive randomized decision tree outputs $+1$ is $1$.

**Proof.** Unfolding the output-conditioned cost, it is the supremum over all inputs of their expected cost when the recursive NAND output is $+1$, with value zero for other inputs. For every input, this quantity is at most $1$: if its output is $+1$, the level-zero input-cost calculation gives cost exactly $1$; otherwise the quantity is zero. Conversely, take the input whose sole sign is $+1$. The level-zero recursive NAND function has output $+1$ there, and its expected query cost is $1$ by the same input-cost calculation. The supremum is therefore at least $1$, proving equality.

**Key facts.** `FABL.recursiveNandRandomizedTree_inputCost_zero`.
