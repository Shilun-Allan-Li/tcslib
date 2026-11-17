<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_stateWord_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State Assignment on One Tape

**Claim.** For every Boolean word $s$, the standard assignment of words to one tape is the constant function with value $s$.

**Proof.** A one-element tape index type has only the index $0$. At that index, the definition of the standard assignment returns $s$, so the two functions agree everywhere.
