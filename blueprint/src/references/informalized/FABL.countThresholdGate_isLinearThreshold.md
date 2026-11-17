<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.countThresholdGate_isLinearThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Count Thresholds Are Linear Thresholds

**Claim.** For a subset $S$ of coordinates and a natural-number threshold $k$, the function that outputs $1$ when at least $k$ coordinates in $S$ are positive and $-1$ otherwise is a linear threshold function.

**Proof.** Choose bias $|S|-2k+1$ and assign coefficient $1$ to each coordinate in $S$ and $0$ to every other coordinate. The weighted sum over the coordinates is therefore the sum of the signs on $S$. By the sign-sum identity (`FABL.sum_signValue_on_eq`), this sum is $2c-|S|$, where $c$ is the number of positive coordinates in $S$. Including the bias gives $2(c-k)+1$. If $c\ge k$, this quantity is nonnegative, so the threshold sign is $1$ (`FABL.thresholdSign_of_nonneg`). If $c<k$, integrality gives $c+1\le k$, making the quantity strictly negative; the threshold sign is then $-1$ (`FABL.thresholdSign_of_neg`). These are exactly the two values of the count threshold gate.

**Key facts.** `FABL.sum_signValue_on_eq`, `FABL.thresholdSign_of_nonneg`, `FABL.thresholdSign_of_neg`.
