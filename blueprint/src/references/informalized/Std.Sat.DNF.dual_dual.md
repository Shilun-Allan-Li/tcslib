<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/DNF.lean :: Std.Sat.DNF.dual_dual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involutivity of DNF dualization

**Claim.** Taking the De Morgan dual of a DNF formula and then dualizing again returns the original formula.

**Proof.** Write the DNF formula as a list of terms. Dualization maps each term and each literal, replacing its Boolean sign by its negation. Dualizing again leaves the list structure in place and negates each sign a second time. Since Boolean negation is involutive, every literal is restored, and hence the entire list of terms, and the formula, is unchanged.
