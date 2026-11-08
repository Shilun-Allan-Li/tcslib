<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean :: Turing.NDTM.AgreeShift.runWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shifted Agreement Under a Choice Word

**Claim.** If two configurations agree with shift $d$ and radius $r+|w|$, then running the same finite choice word $w$ from each yields configurations that agree with shift $d$ and radius $r$.

**Proof.** Induct on the choice word, with the two starting configurations generalized so the induction hypothesis applies after the first choice. For the empty word, running changes neither configuration, and the assumed agreement at radius $r+0$ is exactly what is required. For a word consisting of a bit $b$ followed by a word $w$, running under it is running first one step with choice $b$, then running under $w$ (`runWith_cons`). The one-step preservation theorem (`AgreeShift.stepWith`) reduces the radius by one while preserving the shift. Since the original radius is $r+1+|w|$, the resulting configurations satisfy the induction hypothesis at radius $r+|w|$, which gives the desired agreement after the remaining choices.

**Key facts.** `Turing.NDTM.runWith_cons`, `Turing.NDTM.AgreeShift.stepWith`.
