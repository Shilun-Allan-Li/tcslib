<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.oracleRelabel_computesInTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed computation under state relabeling

**Claim.** Relabeling the states of an oracle Turing machine by a bijection preserves whether it computes a given output from a given input relative to an oracle within $t$ steps.

**Proof.** The relabeled machine's initial configuration is the state relabeling of the original initial configuration. The run-commutation result says that after $t$ steps, its configuration is the state relabeling of the original machine's configuration after $t$ steps (Complexity.oracleRelabel_runFrom). State relabeling changes only the state field: it leaves the output unchanged, and the relabeled state is absent exactly when the original state is absent, since the relabeling is a bijection. Hence the two conditions defining computation within $t$ steps—being halted and having output equal to the specified word—are equivalent.

**Key facts.** `Complexity.oracleRelabel_runFrom`.
