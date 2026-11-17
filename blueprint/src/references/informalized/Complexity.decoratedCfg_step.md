<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger.lean :: Complexity.decoratedCfg_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One step of a decorated configuration

**Claim.** A decorated-machine step updates the original configuration by one original step, updates each extra tape at the designated head's former position according to the visit instruction, records the new data state, and appends the visit output.

**Proof.** The decorated configuration's state is $(q,d)$. Its input symbol is the one scanned by the original configuration; its original-tape symbols are those under the original heads; and its extra-tape symbols are read at the designated original head's position. Consequently, the decorated transition evaluates the original transition and the visit function on exactly the data specified. The original tapes receive the original transition's writes and movements. Each extra tape receives its visit write at the designated head's current position, while its head movement copies the designated original head's movement. The successor state pairs the original successor state with the visit function's new data state. Finally, the output word is extended by the visit function's optional output. Matching these state, input-position, tape-content, head-position, and output fields gives the asserted configuration equality.
