<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.actionBits₂_eq_actionBitsK -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Tape Action Serialization

**Claim.** For every $n$ and every action of a two-work-tape binary machine with state set of size $n+1$, the direct serialization agrees with the general serialization procedure with two work tapes.

**Proof.** The general procedure traverses the finite index list for two tapes, which consists of $0$ followed by $1$. Its work-tape contribution is therefore first the write instruction and head move for tape $0$, then those for tape $1$. This is precisely the order in the direct serialization. Both procedures also place the input-head move first and the output symbol and successor state last, so the complete lists agree.
