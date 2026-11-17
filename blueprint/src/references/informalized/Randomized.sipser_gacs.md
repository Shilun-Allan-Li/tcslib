<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SipserGacs.lean :: Randomized.sipser_gacs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BPP in the Second-Level Classes

**Claim.** If the verifier model is closed under repetition followed by majority vote, answer negation, and the shift-or construction, then every language recognized with bounded error by a verifier in that model belongs to both second-level existential and universal classes defined using polynomial-length witnesses and predicates in the model.

**Proof.** Apply the BPP-to-second-level theorem to the given verifier: closure under majority and shift-or yields membership in the existential second-level class. To obtain the universal-side conclusion, first complement the language. Closure under answer negation converts the original bounded-error verifier into one for the complement. Applying the same BPP-to-second-level theorem to that complement gives its existential second-level membership, which is precisely universal second-level membership for the original language.

**Key facts.** `Randomized.bpp_subset_sigma2`, `Randomized.InBPP.compl`, `Randomized.bpp_subset_sigma2`.
