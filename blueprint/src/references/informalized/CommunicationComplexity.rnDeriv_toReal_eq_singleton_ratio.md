<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/KLDivergence.lean :: CommunicationComplexity.rnDeriv_toReal_eq_singleton_ratio -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative from singleton masses

**Claim.** For finite measures on a finite discrete measurable space, if μ is absolutely continuous with respect to ν and the singleton {ω} has positive ν-mass, then the Radon–Nikodym derivative at ω is the ratio of the singleton masses.

**Proof.** Apply the set-integral formula for the Radon–Nikodym derivative to the singleton {ω}. The integral of a function over a singleton is its value at ω multiplied by the measure of that singleton. Thus ν({ω}) times the real-valued derivative at ω equals μ({ω}). Since ν({ω}) is nonzero, divide by it and rearrange to obtain the stated ratio.
