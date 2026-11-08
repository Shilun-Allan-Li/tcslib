<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.correlatedGaussianMeasure_disagreement -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Disagreement Probability

**Claim.** For $-1\leq\rho\leq1$, the correlated Gaussian measure of the disagreement region is $\arccos(\rho)/\pi$.

**Proof.** First express the disagreement probability as the probability, under two independent standard Gaussians, that the source pair $(U,V)$ satisfies $U(\rho U+\sqrt{1-\rho^2}V)<0$; this is the change-of-variables identity `correlatedGaussianMeasure_disagreement_eq_source`. In polar coordinates, `gaussianSourceDisagreement_polar` identifies this event with an angular set of angles where the signs disagree. The polar integration formula `standardGaussianPlane_measure_angularEvent` then factors its Gaussian probability into the total radial mass times the angular length. The radial mass is $(2\pi)^{-1}$, by `standardGaussianPolarRadialMass_eq`, while `volume_angularDisagreementSet` gives the angular length $2\arccos(\rho)$; the angle lies between $0$ and $\pi$. Multiplying gives $\arccos(\rho)/\pi$.

**Key facts.** `FABL.correlatedGaussianMeasure_disagreement_eq_source`, `FABL.gaussianSourceDisagreement_polar`, `FABL.standardGaussianPlane_measure_angularEvent`, `FABL.standardGaussianPolarRadialMass_eq`, `FABL.volume_angularDisagreementSet`.

**Caveat.** The supplied informal statement discusses a lower-left quadrant probability and Sheppard’s formula, but the formal statement and proof establish the disagreement probability.
