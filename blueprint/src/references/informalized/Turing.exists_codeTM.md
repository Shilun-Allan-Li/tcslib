<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.exists_codeTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Tape Machines in Coded Form

**Claim.** Every finite Boolean machine with exactly one work tape has a machine in code normal form that computes the same Boolean outputs from the same inputs within every time bound.

**Proof.** The stronger coded-machine existence result provides a code normal form machine with the required equivalence of time-bounded computation, together with an additional equality of space usage (`Turing.exists_codeTM_spaceUsed`). Discard the extra space equality and retain its machine and computation equivalence; these are exactly the asserted properties.

**Key facts.** `Turing.exists_codeTM_spaceUsed`.
