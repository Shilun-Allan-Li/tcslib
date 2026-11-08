<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.isSignValued_affineSignFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Sign Functions Are Sign-Valued

**Claim.** For every sign and every vector in the Boolean cube, the affine sign function has absolute value $1$.

**Proof.** Fix an input. The affine sign function evaluates to the product of the chosen sign and the Walsh character at that input (\(\texttt{affineSignFunction\_apply}\)). The Walsh character has absolute value $1$ (\(\texttt{abs\_vectorWalshCharacter}\)), so the product’s absolute value is the absolute value of the chosen sign. Every sign is either $-1$ or $1$ (\(\texttt{signValue\_eq\_neg\_one\_or\_one}\)); in either case its absolute value is $1$.

**Key facts.** `FABL.affineSignFunction_apply`, `FABL.abs_vectorWalshCharacter`, `FABL.signValue_eq_neg_one_or_one`.
