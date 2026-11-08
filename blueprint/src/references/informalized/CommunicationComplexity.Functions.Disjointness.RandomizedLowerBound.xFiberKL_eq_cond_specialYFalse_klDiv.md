<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xFiberKL_eq_cond_specialYFalse_klDiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional Special-Bit Law Under Bob’s Bit Constraint

**Claim.** The formal statement proves that, when the conditional mass of samples with Bob’s special bit false is nonzero, Alice’s special-bit divergence from uniform equals the divergence obtained by first conditioning the fiber measure on that event and then taking Alice’s special-bit law. The supplied informal claim about independence does not match the formal statement.

**Proof.** By definition, Alice’s fiber divergence is the real-valued divergence of her conditional special-bit law from the uniform bit law. The conditional-law identity (`conditionalSpecialXLaw_eq_cond_specialYFalse`) says that, when the mass of the event that Bob’s special bit is false is nonzero, Alice’s law on the fiber equals the law obtained by restricting the fiber measure to that event and mapping to Alice’s special bit. Substituting this identity into the divergence gives the asserted equality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialXLaw_eq_cond_specialYFalse`.

**Caveat.** The supplied informal statement describes an independence claim that is unrelated to the formal theorem and proof source; the claim above follows the formal statement.
