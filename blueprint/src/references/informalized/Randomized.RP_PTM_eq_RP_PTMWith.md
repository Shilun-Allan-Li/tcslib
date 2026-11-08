<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.RP_PTM_eq_RP_PTMWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equivalent One-Sided Time Definitions

**Claim.** The polynomial-time one-sided randomized class with acceptance probability at least $2/3$ on members equals the class defined using the fixed member-input threshold $2/3$.

**Proof.** The two class expressions unfold to the same definition: both range over an exponent and a polynomial time bound of the form $K(n^e+1)$, with the same halting requirement, member acceptance probability $2/3$, and rejection of every random branch on nonmembers. Thus the equality is definitional.
