<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.exists_notHaltedProb_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Small Nonhalting Probability

**Claim.** If halting is prefix-stable and the sum of nonhalting probabilities over every finite initial interval is bounded by $B$, then for every positive rational $\varepsilon$ some time has nonhalting probability at most $\varepsilon$.

**Proof.** The uniform sum bound implies $B\geq0$. Choose a natural number $t>B/\varepsilon$; it is positive. The prefix-stability estimate `notHaltedProb_le_div` gives $\mathrm{notHaltedProb}(r,t)\leq B/t$. Since $t>B/\varepsilon$ and $\varepsilon>0$, we have $B/t<\varepsilon$ (using $B\geq0$), and therefore the desired probability is at most $\varepsilon$.

**Key facts.** `Randomized.ExpTimeLe.nonneg`, `Randomized.notHaltedProb_le_div`.
