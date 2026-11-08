<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.actionBits_eq_actionBitsK -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Tape Action Serialization

**Claim.** For every $n$ and every action of a one-work-tape binary machine with state set of size $n+1$, the direct serialization agrees with the general serialization procedure with one work tape.

**Proof.** In the general procedure, the work-tape data are listed by traversing the finite index list for one tape. That list consists of the sole index $0$, so its contribution is exactly the write instruction and head move for tape $0$. The direct serialization lists the same input-head move first, then this same work-tape data, followed by the output symbol and successor state. The entries and their order therefore agree.
