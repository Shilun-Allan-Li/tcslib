<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_prepare_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication machine preparation

**Claim.** Under the stated encoding, register values, and bounds, the multiplication machine halts with answer true exactly when the input belongs to the encoded multiplication language.

**Proof.** The proof first prepares the registers needed by the multiplication routine. It copies the starting value in register 2 into register 4, then subtracts two from register 4; it copies register 3 into register 5 and likewise subtracts two. These operations produce the encoded end positions for the two factor words. Next it copies register 3 into register 6, halves that value, and subtracts two, giving the total number of multiplication columns, $|a|+|b|$. Each copy and subtraction is justified by the corresponding reachability lemmas, with register bounds maintained throughout. The one halving step is a single machine transition, and its validity and bound conditions follow from the machine’s general precondition lemma and the fact that halving cannot increase a register.

With these registers prepared, the configuration satisfies the multiplication-ready conditions. The canonical multiplication run then halts with the answer given by membership in the multiplication language. Chaining the preparatory reaches to this run proves the result; finite reaches compose and preserve their intermediate-state conditions (via `AReach.halt`).

**Key facts.** `Complexity.mult_copy`, `Complexity.mult_sub_two`, `Complexity.mult_preconditions`, `Complexity.mult_canonical_run`, `Complexity.LogProg.AReach.halt`.
