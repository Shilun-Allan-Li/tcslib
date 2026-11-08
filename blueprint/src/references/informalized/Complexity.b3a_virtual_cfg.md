<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Constructible.lean :: Complexity.b3a_virtual_cfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Virtual Configuration Identification

**Claim.** The virtual configuration formed from the initial configuration of $L$ on input $y$, with boundary tag true, virtual input-head position $1$ on input $x$, and empty output prefix, is the configuration on input $x$ whose state is the initial state of $L$ paired with true, and whose first work tape stores $y$ while every other work tape is blank.

**Proof.** Compare the configuration fields. The state is the initial state of $L$ paired with the true tag, and the input-head position is $1$ on $x$ by the definition of the virtual configuration. For the work tapes, split an index into the added first tape and the tapes inherited from $L$. On the added tape, the buffer stores $y$. On an inherited tape, the initial configuration of $L$ has a blank tape, and the corresponding index is nonzero among the combined tapes, so the right-hand configuration is blank there as well. The tape-head positions also agree: the added tape starts at zero, while each inherited head starts at the initial input position minus one, which is zero at input position $1$. Both output lists are empty.
