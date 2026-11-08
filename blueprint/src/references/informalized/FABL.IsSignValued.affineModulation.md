<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.IsSignValued.affineModulation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Modulation Preserves Sign Values

**Claim.** Multiplying a sign-valued function by a fixed sign and a Walsh character preserves absolute value one at every input.

**Proof.** Fix an input $x$. The absolute value of the modulated function is the product of the absolute values of its three factors. The Walsh character has absolute value one (`abs_vectorWalshCharacter`), and the original function does as well by hypothesis. The fixed sign is either $-1$ or $1$ (`signValue_eq_neg_one_or_one`), hence also has absolute value one. Their product therefore has absolute value one.

**Key facts.** `FABL.abs_vectorWalshCharacter`, `FABL.signValue_eq_neg_one_or_one`.
