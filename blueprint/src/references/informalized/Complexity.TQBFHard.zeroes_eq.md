<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardParams.lean :: Complexity.TQBFHard.zeroes_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output of the Zero Transducer

**Claim.** For every finite bit string $l$, the transducer that emits false on each input bit outputs exactly $l.length$ false bits.

**Proof.** Use induction on $l$. For the empty string, the transducer outputs the empty string, which is the list of zero false bits. For a cons string $b::l$, the first input bit emits one false, and the machine then processes $l$ with the same state. By the induction hypothesis that remainder contributes $l.length$ false bits. Their concatenation is a list of $l.length+1$ false bits, as required.
