<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.pcfg_fA -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition from the First Field State

**Claim.** Under the stated bounds on $p$ and the assumption that the symbol of $y$ at position $p-1$ is $b$, one step from the configuration in state $fA$ produces the configuration in state $fB$, retains the auxiliary words and output, and advances the input head to position $p+1$.

**Proof.** First use the configuration-step identity (`pcfg_step`) to express the machine's transition from the configuration at input position $p$ as the action selected by the transition table using the input symbol at position $p-1$. The hypothesis identifies that symbol as $b$. In state $fA$, on input symbol $b$, the transition table selects a positive input-head move, leaves all three auxiliary tapes idle, produces no output, and changes the state to $fB$ while retaining $f$ and the bit vector. Applying the action to the configuration leaves the auxiliary words and output unchanged and moves the input head according to that positive move; the identity for applying an idle auxiliary action (`tact_idle_apply`) makes these effects explicit. Finally, the positive move sends the head position $fpos(y,p)$ to $fpos(y,p+1)$ by `moveInputPos_fpos`, using $p\le |y|$. This is precisely the claimed next configuration.

**Key facts.** `Complexity.Meyer.pcfg_step`, `Complexity.Meyer.tact_idle_apply`, `Complexity.Meyer.moveInputPos_fpos`.
