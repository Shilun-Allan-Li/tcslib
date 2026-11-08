<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.decrementTM_tr_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input independence of the decrement transition

**Claim.** For any number of work tapes, tape index, phase, and assignment of optional Boolean work-head symbols, the decrement machine's transition action is the same for every optional Boolean input symbol.

**Proof.** The increment machine's transition is defined using only the current phase and the work-head symbols; it does not inspect the input symbol. The decrement machine is obtained by relabeling work symbols in that transition, which leaves this independence unchanged. Hence changing the optional input symbol does not change the transition action.
