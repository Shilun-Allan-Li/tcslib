<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.originalBLRTester_oddSymmetrizedAcceptanceProbability_eq_oddBLR -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-symmetrized BLR identity

**Claim.** For every $n$ and every function $f$ valued in $[-1,1]$, independently symmetrizing each of the original BLR tester's three queries by a uniform sign flip gives the same acceptance probability as the zero-noise Håstad tester on $f$.

**Proof.** First replace the symmetrized acceptance probability by the acceptance probability of the original tester applied to the odd part of $f$; averaging over independent query sign flips has exactly this effect (\texttt{FABL.SignTester.oddSymmetrizedAcceptanceProbability\_eq\_oddPart}). The original tester's Fourier formula expresses this as $\frac12+\frac12$ times the sum of cubes of all Fourier coefficients of the odd part (\texttt{FABL.originalBLRTester\_acceptanceProbability\_eq\_fourierSum}). The Håstad acceptance formula at zero noise is $\frac12+\frac12$ times the sum, over odd-cardinality sets, of the cubes of the Fourier coefficients of $f$ (\texttt{FABL.hastadAcceptanceProbability\_eq\_fourierSum}); its noise weight is $1$.

It remains to identify these sums. For even-cardinality sets, the odd part's Fourier coefficient is zero (\texttt{FABL.fourierCoeff\_oddPart\_of\_even}), so those terms vanish. For odd-cardinality sets, that coefficient equals the coefficient of $f$ (\texttt{FABL.fourierCoeff\_oddPart\_of\_odd}). Thus the full sum for the odd part equals the sum restricted to odd-cardinality sets for $f$, proving the identity.

**Key facts.** `FABL.SignTester.oddSymmetrizedAcceptanceProbability_eq_oddPart`, `FABL.originalBLRTester_acceptanceProbability_eq_fourierSum`, `FABL.hastadAcceptanceProbability_eq_fourierSum`, `FABL.fourierCoeff_oddPart_of_even`, `FABL.fourierCoeff_oddPart_of_odd`.
