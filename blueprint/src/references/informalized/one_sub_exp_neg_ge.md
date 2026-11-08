<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Basic.lean :: one_sub_exp_neg_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential lower bound

**Claim.** For every $\eta>0$, $1-e^{-\eta}\ge \eta-\eta^2/2$.

**Proof.** The quadratic upper bound on the negative exponential gives $e^{-\eta}\le 1-\eta+\eta^2/2$ for $\eta\ge0$ (\texttt{exp\_neg\_le\_quadratic}). Rearranging this inequality gives the claimed lower bound.

**Key facts.** `exp_neg_le_quadratic`.
