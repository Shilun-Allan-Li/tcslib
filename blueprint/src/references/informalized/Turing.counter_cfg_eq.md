<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_cfg_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Configuration Components

**Claim.** Adjoining the counter tape to a configuration leaves its input-head position and output unchanged, preserves the original work tapes and their head positions in the first $k$ slots, and places the given counter tape and head in the last slot.

**Proof.** The counter-layout identity expresses the enlarged configuration explicitly: its input position and output are those of the original configuration, while its work-tape functions are the original ones on the first $k$ slots and the supplied counter tape on the last slot. The same description applies to head positions, with the original heads in the first slots and the supplied counter head last. This is the stated componentwise equality.

**Key facts.** `Turing.counter_layout`.
