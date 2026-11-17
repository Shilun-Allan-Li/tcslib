<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_result_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a product result bit

**Claim.** From the result-test state, the machine reaches the parity state labelled by the bit of $x$ at register 12’s index, while maintaining its validity and register-bound conditions at every intermediate step.

**Proof.** The result-test instruction compares registers 12 and 1. If they are equal, then register 12 is the input length, so the defaulted bit at that position is false; the machine therefore reaches the false parity state immediately. Otherwise it enters the result-read state and queries the bit oracle using register 12. A whole-input query with one register produces the encoding of $x$ paired with that register’s binary value (`vword_whole₁`), and the oracle query fact identifies the answer with the defaulted bit of $x$ at that position (`mult_queries`). Thus the next state is the parity state labelled by the desired bit. The one-step reaches satisfy the intermediate conditions using the machine precondition lemma and the assumed register bound; the immediate branch is completed by reflexive reachability, and the preceding transition is then attached by the reachability step rule.

**Key facts.** `Complexity.mult_preconditions`, `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.vword_whole₁`, `Complexity.mult_queries`, `Complexity.LogProg.AReach.single`, `Complexity.LogProg.AReach.step`.
