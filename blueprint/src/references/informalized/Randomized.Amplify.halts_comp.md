<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.halts_comp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting Under Simulation Composition

**Claim.** If each nonhalting step of $M$ from the image under $\varphi$ agrees with the image of the corresponding step of $N$, and every choice word of length $m$ halts $M$ from the image of any halting configuration of $N$, then halting of all length-$n$ runs of $N$ implies halting of all length-$(n+m)$ runs of $M$ from the corresponding image.

**Proof.** Apply the position-bounded composition result `halts_comp_pos` with a bound larger than the input-head position of the starting configuration plus $n$. Such a natural-number bound exists. The step-agreement assumption supplies its simulation hypothesis, and the stated halting condition for images of halting configurations supplies its final-phase hypothesis; that condition needs no additional position restriction. The assumed length-$n$ halting property of $N$ then gives the conclusion for every choice word of length $n+m$.

**Key facts.** `Randomized.Amplify.halts_comp_pos`.
