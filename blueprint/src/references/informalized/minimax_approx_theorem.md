<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/FiniteMinimax.lean :: minimax_approx_theorem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Approximate mixed-strategy minimax inequality

**Claim.** For every positive tolerance, there are mixed strategies $p$ and $q$ such that every pure-column payoff against $p$, with the tolerance added, is at least every pure-row payoff against $q$.

**Proof.** Fix $\varepsilon>0$. The approximate minimax theorem for the game supplies mixed strategies $p$ and $q$ such that, for every pure row $i$ and pure column $j$, $\operatorname{payoffVsPure}(G,p,j)+\varepsilon\ge\operatorname{pureVsPayoff}(G,i,q)$. This is exactly the required conclusion.

**Key facts.** `approx_minimax`.

**Caveat.** The supplied prose describes an exact von Neumann minmax theorem, but the formal statement and proof establish only the displayed approximate pure-action inequality.
