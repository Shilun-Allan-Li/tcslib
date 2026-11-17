<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean :: Complexity.LogProg.SavitchARM.Inv.setM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Midpoint update preserves the invariant

**Claim.** Replacing the midpoint register by any $M'\le 2^w$ preserves the invariant with parameters $s,w,i$.

**Proof.** The update changes only the midpoint register. Every invariant condition concerning another register therefore remains true from the original invariant. The midpoint condition for the updated state is exactly the assumed inequality $M'\le 2^w$. Together these are all the invariant conditions for the new state.
