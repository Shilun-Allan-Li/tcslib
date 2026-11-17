<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dgCost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper bound on construction cost

**Claim.** For $k>0$, $n\le 2t+1$, and either choice of the Boolean parameters $\ell$ and $r$, the stated construction cost is at most $(4t+7)k+4$.

**Proof.** Multiply $n\le 2t+1$ by the positive natural number $k$ to obtain $nk\le (2t+1)k$. Now consider the four possible pairs $(\ell,r)$. For each pair, their Boolean values contribute either zero or one to the cost, so substituting those values reduces the desired bound to an inequality between natural-number sums and products. Using $nk\le (2t+1)k$ and rearranging the resulting expressions gives the claimed upper bound in each case.
