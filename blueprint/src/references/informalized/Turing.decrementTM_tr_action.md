<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.decrementTM_tr_action -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decrement transition action

**Claim.** For any number of work tapes, tape index, phase, optional input symbol, and work-head symbols, the decrement machine keeps the input head stationary and never instructs any work tape to write a blank.

**Proof.** Unfold the definition of decrement as increment with Boolean symbols relabeled by complementation. The increment transition has input movement zero in every phase and branch. Its work-tape instructions either write a Boolean symbol on the selected tape or make no write; on every other tape they make no write as well. Relabeling Boolean symbols preserves this distinction, so no tape receives the instruction to write a blank. The required claims follow in each phase after distinguishing whether the selected head reads true, false, or no symbol.
