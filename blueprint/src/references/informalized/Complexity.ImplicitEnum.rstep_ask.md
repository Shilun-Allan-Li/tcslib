<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean :: Complexity.ImplicitEnum.rstep_ask -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition from the Asking State

**Claim.** From the asking configuration with input $x$, output $u$, and counter $i$, one step leaves the output and counter unchanged and enters the bit state if the oracle accepts the encoded pair, or the halted state otherwise.

**Proof.** In the asking state, the program makes a call to decider $0$, with the whole input and register $0$ as its single argument. The virtual input for this call is exactly $\langle x,\operatorname{bits}(i)\rangle$, by the register-call encoding fact (`vword_call`). The call transition therefore chooses the positive successor, the bit state, precisely when the oracle accepts this word, and otherwise chooses the halted state. The call leaves the output and register unchanged, giving the asserted configuration; the state field of a configuration is the named state stored as an option (`cfg_state`).

**Key facts.** `Complexity.ImplicitEnum.cfg_state`, `Complexity.ImplicitEnum.vword_call`.
