<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_regular -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement Outside Record States

**Claim.** For every control state that is not a fully decoded transition-record state, and every input symbol and four-tape read tuple, the stopped interpreter and the original interpreter have identical transition actions.

**Proof.** Exhaust the constructors of the control state. For every constructor other than the pending-action constructor `applyRecord`, the two transition functions reduce to the same definition, so their actions agree. In the `applyRecord` case, the hypothesis says that the chosen control state differs from every `applyRecord bits halt`; taking the actual register and halt flag contradicts that inequality, so this case cannot occur.
