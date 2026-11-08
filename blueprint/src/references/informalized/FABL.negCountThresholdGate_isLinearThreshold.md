<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.negCountThresholdGate_isLinearThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative-count threshold is linear

**Claim.** The gate that outputs $-1$ when at least $k$ coordinates of $S$ are positive, and $1$ otherwise, is a linear threshold function.

**Proof.** Give each coordinate in $S$ weight $-1$, each coordinate outside $S$ weight $0$, and choose offset $-|S|+2k-1$. The resulting affine form is the offset minus the sum of the signs on $S$. By the sign-sum identity, that sum is twice the number of positive coordinates in $S$ minus $|S|$ (`sum_signValue_on_eq`). Hence the affine form equals $2k-1-2r$, where $r$ is that positive-coordinate count. If $r\ge k$, this is negative, so its threshold sign is $-1$ (`thresholdSign_of_neg`), matching the gate. If $r<k$, then $r+1\le k$, making the affine form nonnegative; its threshold sign is $1$ (`thresholdSign_of_nonneg`), again matching the gate.

**Key facts.** `FABL.sum_signValue_on_eq`, `FABL.thresholdSign_of_neg`, `FABL.thresholdSign_of_nonneg`.
