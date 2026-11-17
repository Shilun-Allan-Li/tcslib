<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun.lean :: Randomized.PolyAmp.ampOr_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Configuration Code Test

**Claim.** Under the space bounds and reachability hypothesis, the one-step-language indicator on the specified encoding equals the Boolean decision that $c'$ is the code of either one-step successor of $C$.

**Proof.** First express the language indicator as the decision of membership (`indicator_eq_decide`). The one-step membership characterization says that membership is equivalent to the existence of a choice bit $b$ for which $c'$ is the code of the configuration reached by stepping from $C$ with $b$ (`mem_stepLang_iff`). Since $b$ is Boolean, its two possibilities are true and false. Thus this existential condition is equivalent to the disjunction that $c'$ equals the true-choice successor code or the false-choice successor code, yielding the stated equality of decisions.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`, `Randomized.PolyAmp.mem_stepLang_iff`.
