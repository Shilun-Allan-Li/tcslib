<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.innerProductLinearPCPPSystem_isPCPP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner product PCPP guarantee

**Claim.** For every positive natural number $m$, the specified verifier has rejection rate $1/4$ for the inner product modulo two property: satisfying words have a proof accepted with probability $1$, and words farther than $\varepsilon$ from every satisfying word are rejected with probability strictly greater than $\varepsilon/4$.

**Proof.** First, the rate is positive. For completeness, take the proof recording each coordinatewise product and the successive prefix sums. The checks of the initial and final prefix values, the product at every coordinate, and each prefix recurrence all pass when the word's inner product is $1$ (`innerProductLinearProof_checks`). Thus the rejection probability of this proof is zero, so its acceptance probability is one.

For soundness, let $w$ be farther than $\varepsilon$ from every satisfying word, and fix any proof. Then $w$ itself cannot satisfy the property: otherwise its distance from itself is zero, contradicting the assumed distance condition. Since the proof's checks all being true would imply that $w$ satisfies the property (`isInnerProductModTwoOne_of_linearChecks`), at least one seed check fails. Moreover, flipping to the designated neighboring word changes the inner product to $1$ (`innerProductFlipNeighbor_isInnerProductModTwoOne`), and this neighbor differs from $w$ in relative Hamming distance at most $1/m$ (`relativeHammingDist_innerProductFlipNeighbor_le_one_div`). The distance hypothesis therefore gives $\varepsilon<1/m$, or $\varepsilon m<1$.

The seeds are uniform, and the verifier's rejection probability is exactly the fraction of seeds whose checks fail (`innerProductLinearPCPPSystem_rejectionProbability`). There are $2m+2$ seeds, so one failed seed gives rejection probability at least $1/(2m+2)$ (`one_div_checkCount_le_innerProduct_failedCheckProbability`). From $\varepsilon m<1$ and $0\le\varepsilon\le1$, it follows that $\varepsilon/4<1/(2m+2)$. Combining these bounds proves the required strict rejection inequality.

**Key facts.** `FABL.innerProductLinearProof_checks`, `FABL.isInnerProductModTwoOne_of_linearChecks`, `FABL.innerProductFlipNeighbor_isInnerProductModTwoOne`, `FABL.relativeHammingDist_innerProductFlipNeighbor_le_one_div`, `FABL.innerProductLinearPCPPSystem_rejectionProbability`, `FABL.one_div_checkCount_le_innerProduct_failedCheckProbability`.
