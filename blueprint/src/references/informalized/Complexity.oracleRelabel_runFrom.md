<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.oracleRelabel_runFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relabeling commutes with oracle runs

**Claim.** For a machine whose states are relabeled by a bijection, running the relabeled machine for $t$ steps from a relabeled configuration gives the relabeling of the original machine's configuration after $t$ steps.

**Proof.** First, one oracle step commutes with state relabeling (Complexity.oracleRelabel_step). Applying this identity successively shows that every iterate of the relabeled step map agrees with relabeling after the corresponding iterate of the original step map. In particular, this holds for the $t$th iterates, which are the two runs in the claim.

**Key facts.** `Complexity.oracleRelabel_step`.
