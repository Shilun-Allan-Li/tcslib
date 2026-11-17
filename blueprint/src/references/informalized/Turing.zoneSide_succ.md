<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneSide_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Side Word at Successor Length

**Claim.** For $n+1$ indices, the side word is the list at index $0$ followed by the side word formed from the successor indices.

**Proof.** In the defining concatenation over the finite range of indices, separate the index-zero term from the successor indices. The remaining terms are precisely the lists indexed by successors, in their original order; hence the full side word is $w(0)$ followed by the side word of the successor-indexed family.
