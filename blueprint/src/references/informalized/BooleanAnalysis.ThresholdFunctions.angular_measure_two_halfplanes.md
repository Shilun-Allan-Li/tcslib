<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianPolar.lean :: BooleanAnalysis.ThresholdFunctions.angular_measure_two_halfplanes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Angular Overlap of Two Halfplanes

**Claim.** For $0\le\alpha\le\pi$, the measure of angles in $(-\pi,\pi)$ for which both $\cos\theta$ and $\cos(\theta-\alpha)$ are nonpositive is $\pi-\alpha$.

**Proof.** Write $\Theta$ for the set where both cosine inequalities hold. Within $(-\pi,\pi)$, the first inequality forces $\theta$ into either the left interval $(-\pi,-\pi/2]$ or the right interval $[\pi/2,\pi)$, by the characterization of where cosine is nonpositive (`cos_nonpos_iff_of_mem_Ioo`). The two pieces are disjoint and measurable (`measurableSet_twoHalfplaneAngles`).

On the left piece, the second cosine condition cuts the interval off below at $a_1=\max(-\pi,\alpha-3\pi/2)$. The cosine characterizations on the relevant ranges (`cos_nonpos_iff_of_le_neg_pi_div_two`) show that the piece lies between $a_1$ and $-\pi/2$, up to endpoints; conversely, the open interval from $a_1$ to $-\pi/2$ satisfies both conditions. Since endpoints have measure zero, this piece has measure $-\pi/2-a_1$.

On the right piece, the second condition gives the interval from $a_2=\max(\pi/2,\alpha+\pi/2)$ to $\pi$, with at most one additional endpoint. The range characterization (`cos_nonpos_iff_of_neg_pi_div_two_le`) establishes these inclusions, and the singleton contributes zero measure, so this piece has measure $\pi-a_2$. Adding the two measures gives the total overlap. If $\alpha\le\pi/2$, then $a_1=-\pi$ and $a_2=\alpha+\pi/2$, so the sum is $\pi-\alpha$. If $\alpha>\pi/2$, then $a_1=\alpha-3\pi/2$ and $a_2=\alpha+\pi/2$; the right piece has zero length and the left piece has length $\pi-\alpha$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.measurableSet_twoHalfplaneAngles`, `BooleanAnalysis.ThresholdFunctions.cos_nonpos_iff_of_mem_Ioo`, `BooleanAnalysis.ThresholdFunctions.cos_nonpos_iff_of_le_neg_pi_div_two`, `BooleanAnalysis.ThresholdFunctions.cos_nonpos_iff_of_neg_pi_div_two_le`.
