<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerComplete.lean :: Complexity.Meyer.st_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State Answer Characterizes the Run

**Claim.** For every state-and-output-register pair $\sigma$ and every $t<2^W$, the answer for $\mathrm{st}(\sigma)$ at $(t,0)$ is true exactly when $\sigma$ is the state-and-output-register summary of the configuration reached after $t$ steps.

**Proof.** The table agreement hypothesis identifies the answer with the tabulated state answer for the configuration reached at time $t$; the index bound needed for this application is $0<2^W$. The state-answer rule (`Complexity.Meyer.tabAns_st`) says this tabulated value is true exactly when both the configuration's state and its output-register summary equal the corresponding components of $\sigma$. These two component equalities are equivalent to equality of the ordered pairs. Hence the Boolean answer agrees with the decision of whether $\sigma$ is the run's summary.

**Key facts.** `Complexity.Meyer.tabAns_st`.
