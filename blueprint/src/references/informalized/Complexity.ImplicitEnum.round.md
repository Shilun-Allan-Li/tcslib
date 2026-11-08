<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean :: Complexity.ImplicitEnum.round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Enumeration Round

**Claim.** If $i$ is below the output length and the stated bounds hold, the enumerator runs from its asking configuration with the first $i$ output bits and counter $i$ to the asking configuration with the first $i+1$ bits and counter $i+1$, with every earlier configuration satisfying the prescribed shape bounds.

**Proof.** Write $b$ for the $i$-th bit of $f(x)$. The length oracle answers positively because $i<|f(x)|$, so the first step moves from asking to the bit state without changing the output or counter (`rstep_ask`). The bit oracle returns $b$, and the next step enters the state that emits $b$ (`rstep_bit`). Emitting that bit appends it to the output and enters the counter-increment state; the output is now the first $i+1$ bits, since taking $i+1$ entries is taking the first $i$ and appending the $i$-th bit. The increment routine then returns the machine to asking with counter $i+1$, by `inc_run`; identifying its register updates with the corresponding enumerator configurations uses `regCfg_cfg`. Concatenating these three initial steps with the increment run gives the claimed finite run (`rrun_add`). For the shape bound, the initial and first-step configurations have asking or bit state and counter $i\le F$. The next configuration is in an emitting state, and all subsequent configurations before the endpoint are covered by `inc_run`: their states are the increment states and their head positions lie between $-1$ and the bit length of $i+1$, which is at most $W$. Those states have no oracle call, so these configurations satisfy the second clause of Shape.

**Key facts.** `Complexity.ImplicitEnum.rstep_ask`, `Complexity.ImplicitEnum.rstep_bit`, `Complexity.LogProg.inc_run`, `Complexity.ImplicitEnum.regCfg_cfg`, `Complexity.LogProg.rrun_add`.
