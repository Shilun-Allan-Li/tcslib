<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.two_mul_relativeHammingDist_coordinateJuntaApproximation_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate junta approximation bound

**Claim.** The relative Hamming distance from a Boolean function to its coordinate junta approximation is at most half the Fourier weight outside the sets of coordinates contained in \(J\).

**Proof.** Write \(p\) for the Boolean coordinate projection of \(f\) onto \(J\), and \(q\) for the rounded Boolean junta approximation. For sign-valued functions, their uniform inner product equals one minus twice their relative Hamming distance (\(\texttt{FABL.uniformInner_eq_one_sub_two_mul_relativeHammingDist}\)). The projection captures the inner product of \(f\) with its rounded approximation (\(\texttt{FABL.uniformInner_coordinateJuntaApproximation}\)); that inner product is the uniform expectation of \(|p|\) (\(\texttt{FABL.uniformInner_projection_rounding_eq_expect_abs}\)). The projection's squared uniform norm is at most this same expectation (\(\texttt{FABL.uniformInner_projection_self_le_expect_abs}\)), and its squared norm equals one minus the Fourier weight outside the subsets of \(J\) (\(\texttt{FABL.uniformInner_booleanCoordinateProjection_self}\)). Combining these identities and inequality gives \(1-2d\ge 1-W\), where \(d\) is the relative Hamming distance and \(W\) is that outside Fourier weight. Hence \(2d\le W\).

**Key facts.** `FABL.uniformInner_eq_one_sub_two_mul_relativeHammingDist`, `FABL.uniformInner_coordinateJuntaApproximation`, `FABL.uniformInner_projection_rounding_eq_expect_abs`, `FABL.uniformInner_projection_self_le_expect_abs`, `FABL.uniformInner_booleanCoordinateProjection_self`.
