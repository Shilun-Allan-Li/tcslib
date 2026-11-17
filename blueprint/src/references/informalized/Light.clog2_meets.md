<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Logs.lean :: Light.clog2_meets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic Computation by a Program

**Claim.** If procedure $p$ contains the specified logarithm-computation body and $2x+1\le\mathrm{word}(\mathrm{lim})$, then calling it with input $x$ finishes within $12\,\mathrm{clog}(2,x)+10$ steps, returns $\mathrm{clog}(2,x)$ in location $0$, and leaves memory unchanged.

**Proof.** The body lookup reduces the claim to executing the specified body. Set the candidate $L$ to $0$ and the power $q$ to $1$. For the loop, use the invariant that before round $i$, the state has $L=i$, $q=2^i$, input $x$, and unchanged memory. For every $i<\mathrm{clog}(2,x)$, the characterization of the base-two ceiling logarithm gives $2^i<x$ (`Nat.lt_clog_iff_pow_lt`), so the loop condition holds. Doubling $q$ and incrementing $L$ establish the invariant for the next round; the word bound ensures the required expressions are safe. At $i=\mathrm{clog}(2,x)$, the bound $x\le2^{\mathrm{clog}(2,x)}$ (`Nat.le_pow_clog`) makes the loop condition false. The final assignment places $L$ in the argument location and leaves memory unchanged. `Ends.whileBlock` accounts for the loop rounds and their cost; `Ends.next` combines them with the surrounding assignments, and `Meets.of_body` gives the call-level conclusion.

**Key facts.** `Light.Meets.of_body`, `Light.Ends.next`, `Light.Ends.whileBlock`, `Light.update_frame_setLocal`.
