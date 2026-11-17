<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean :: Complexity.LogProg.ISGen.one_le_card_rset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty Reachable-Code Set

**Claim.** For every window radius $s$, the finite set of codes reachable from the initial configuration has cardinality at least one.

**Proof.** The initial code reaches itself by the length-zero path, using reflexivity of reflexive-transitive reachability. The characterization of membership in the reachable-code set (`Complexity.ExpBFS.mem_rset`) places that code in the set. Thus the set is nonempty, and a nonempty finite set has cardinality at least one.

**Key facts.** `Complexity.ExpBFS.mem_rset`.
