<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.SignTester.noisePreprocessed_usesPredicates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Predicate Preservation

**Claim.** If every check selected by a tester uses a predicate in $\Psi$, then every check selected by its noise-preprocessed tester also uses a predicate in $\Psi$.

**Proof.** A seed of the preprocessed tester consists of an original seed together with the newly sampled noisy queries. The check attached to this pair retains the predicate of the original seed's check. Therefore the original hypothesis that every seed selects a predicate in $\Psi$ applies to the first component, proving the claim.
