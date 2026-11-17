<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.cfgIdx_cases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exhaustive Tableau Index Cases

**Claim.** Every index below $(T+1)(k(2T+1)+N+3)$ represents a work-tape cell, an input position, or a snapshot at some time at most $T$, with the indicated bounds on tape offset or input position.

**Proof.** Write $S=k(2T+1)+N+3$ for the stride. Since $S>0$, divide $i$ by $S$: its quotient is at most $T$, and its remainder is less than $S$. The quotient gives the time, while the remainder lies in exactly one of three consecutive regions. If it is below $k(2T+1)$, divide it by $2T+1$; the quotient is a work-tape number below $k$, hence a tape index, and the remainder is an offset below $2T+1$. The division algorithm then reconstructs the index as the corresponding work-cell index. Otherwise, if the remainder is below $k(2T+1)+N+2$, subtract the work-cell region's length; the result is an input position below $N+2$, and adding that region back reconstructs the input-position index. In the final case the remainder is at least $k(2T+1)+N+2$ but less than $S$, so it equals that endpoint exactly. This is the snapshot slot, giving the snapshot index at the quotient time.

**Key facts.** `Complexity.stride_pos`.
