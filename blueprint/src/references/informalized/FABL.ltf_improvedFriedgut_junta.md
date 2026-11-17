<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.ltf_improvedFriedgut_junta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Improved junta approximation for threshold functions

**Claim.** A linear threshold Boolean function admits a junta approximation with the stated size bound, with all but $2\varepsilon$ of its Fourier weight concentrated on low-degree sets supported on the junta coordinates, and relative Hamming distance at most $\varepsilon$.

**Proof.** Split according to whether the total influence is zero. If it is zero, take $J=\varnothing$ and $g=f$. The zero-influence junta result makes $f$ a junta on no coordinates (`isKJunta_zero_of_totalInfluence_eq_zero`), and the spectrum is concentrated on sets supported on the empty set (`spectrum_concentrated_on_empty_of_totalInfluence_eq_zero`); restricting further to sets of degree at most the prescribed cutoff does not affect this claim. The size bound reduces to $0\le1$, and the distance from $f$ to itself is zero. If total influence is nonzero, its nonnegativity implies it is positive (`totalInfluence_nonneg`). The threshold-function spectrum concentration result supplies concentration up to degree $\lceil16/\varepsilon^2\rceil$ (`ltf_spectrum_concentrated_up_to_improvedFriedgutDegree`). Apply the improved Friedgut junta theorem with this degree cutoff and the positive total influence. It produces a coordinate set and a junta function with the required spectral concentration and distance bound, and a size bounded by the junta size term. The theorem's size bound is at most one plus that term, which is the stated bound.

**Key facts.** `FABL.totalInfluence_nonneg`, `FABL.isKJunta_zero_of_totalInfluence_eq_zero`, `FABL.spectrum_concentrated_on_empty_of_totalInfluence_eq_zero`, `FABL.ltf_spectrum_concentrated_up_to_improvedFriedgutDegree`, `FABL.improvedFriedgut_exists_close_junta`.
