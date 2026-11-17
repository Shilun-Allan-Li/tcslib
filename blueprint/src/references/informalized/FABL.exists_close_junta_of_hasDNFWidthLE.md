<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.exists_close_junta_of_hasDNFWidthLE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A close junta for a bounded-width DNF

**Claim.** If a Boolean function has a representation by a DNF of width at most $w$, then for $0<\varepsilon\le1$ there is a junta $g$ close to it in relative Hamming distance, with its number of relevant coordinates bounded by the stated DNF junta-size bound.

**Proof.** Split into the cases of zero and positive total influence. If the total influence is zero, the function is already a $0$-junta ($\mathrm{isKJunta\_zero\_of\_totalInfluence\_eq\_zero}$); choose it as $g$ and take the empty coordinate set. The distance is zero, and the size bound is positive. If the total influence is positive, let $k$ be the DNF degree threshold and let $J$ be the coordinates selected by the influence-threshold construction. Choose the coordinate-junta approximation on $J$. It is a junta on $J$ ($\mathrm{coordinateJuntaApproximation\_isKJunta}$), and the concentration of the DNF's Fourier spectrum through degree $k$ gives relative Hamming distance at most $\varepsilon$ ($\mathrm{dnf\_spectrum\_concentrated\_up\_to\_dnfFriedgutDegree}$ and $\mathrm{theorem9\_28\_close\_to\_coordinateJunta}$). For its size, the threshold construction bounds $|J|$ by $I^3\varepsilon^{-2}9^k$, where $I$ is the total influence ($\mathrm{card\_theorem9\_28\_influentialCoordinates\_le}$). The width bound gives $I\le2w$ ($\mathrm{totalInfluence\_le\_two\_mul\_of\_hasDNFWidthLE}$); nonnegativity of total influence permits cubing this inequality ($\mathrm{totalInfluence\_nonneg}$). Substitution yields $|J|\le(2w)^3\varepsilon^{-2}9^k$, which is at most the claimed bound.

**Key facts.** `FABL.isKJunta_zero_of_totalInfluence_eq_zero`, `FABL.coordinateJuntaApproximation_isKJunta`, `FABL.dnf_spectrum_concentrated_up_to_dnfFriedgutDegree`, `FABL.theorem9_28_close_to_coordinateJunta`, `FABL.card_theorem9_28_influentialCoordinates_le`, `FABL.totalInfluence_le_two_mul_of_hasDNFWidthLE`, `FABL.totalInfluence_nonneg`.

**Caveat.** The supplied informal statement includes general Fourier concentration and LTF claims; this proof establishes the specific width-bounded DNF junta approximation stated in the formal theorem.
