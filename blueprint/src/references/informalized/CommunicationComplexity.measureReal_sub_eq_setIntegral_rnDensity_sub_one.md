<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.measureReal_sub_eq_setIntegral_rnDensity_sub_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measure difference as an integral

**Claim.** If $\mu$ and $\nu$ are probability measures and $\mu\ll\nu$, then for every set $S$, $\mu(S)-\nu(S)=\int_S ((d\mu/d\nu)(x)-1)\,d\nu(x)$, where the density is real-valued.

**Proof.** First, the real-valued density is integrable with respect to $\nu$; restricting the measure to $S$ preserves integrability because the restricted measure is bounded above by $\nu$. The constant function $1$ is also integrable on this restriction. Linearity of the integral therefore writes the integral of density minus one as the difference of the two set integrals. The Radon–Nikodym set-integral formula identifies the density integral with $\mu(S)$, and the set integral of the constant one is $\nu(S)$. These identifications give the asserted equality.

**Key facts.** `CommunicationComplexity.integrable_rnDensity`.
