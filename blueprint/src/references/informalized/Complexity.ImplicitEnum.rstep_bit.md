<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean :: Complexity.ImplicitEnum.rstep_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition from the Bit State

**Claim.** From the bit-state configuration with input $x$, output $u$, and counter $i$, one step leaves the output and counter unchanged and enters the state that emits true or false according to the oracle's answer on decider $1$.

**Proof.** In the bit state, the program calls decider $1$ on the whole input and register $0$. The virtual input is $\langle x,\operatorname{bits}(i)\rangle$ by the register-call encoding fact (`vword_call`). Thus the call selects the positive successor, the true-emitting state, exactly when the oracle accepts this encoded pair; otherwise it selects the false-emitting state. The output and register are unchanged by this call, so the resulting configuration has the claimed form; `cfg_state` identifies its state field.

**Key facts.** `Complexity.ImplicitEnum.cfg_state`, `Complexity.ImplicitEnum.vword_call`.
