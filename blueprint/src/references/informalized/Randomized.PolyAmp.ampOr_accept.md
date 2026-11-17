<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun.lean :: Randomized.PolyAmp.ampOr_accept -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Test for Reachable Configurations

**Claim.** Under the space bounds and reachability hypothesis, the acceptance-language indicator on the specified encoding equals the Boolean decision of whether $C$ is accepting.

**Proof.** The indicator of a language at an input equals the decision of membership in that language (`indicator_eq_decide`). For the given encoding, the membership characterization of the acceptance-configuration language says that membership is equivalent to $C$ being accepting, provided the machine’s space bound and the reachability hypothesis hold (`mem_acceptLang_iff`). Deciding equivalent propositions gives the claimed equality of Booleans.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`, `Randomized.PolyAmp.mem_acceptLang_iff`.
