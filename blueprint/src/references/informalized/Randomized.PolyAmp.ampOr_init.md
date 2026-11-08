<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun.lean :: Randomized.PolyAmp.ampOr_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration Code Test

**Claim.** The initialization-language indicator on the encoding of $x,c,S$ equals the Boolean decision that $c$ is the code of the initial configuration on $x$ with window size $S$.

**Proof.** Replace the language indicator by the decision of membership (`indicator_eq_decide`). The membership characterization for the initialization language identifies membership of this encoding exactly with the equality between $c$ and the code of the initial configuration at window size $S$ (`mem_initLang_iff`). The resulting decisions are therefore equal.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`, `Randomized.PolyAmp.mem_initLang_iff`.
