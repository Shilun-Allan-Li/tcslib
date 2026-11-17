<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenLoop.lean :: Complexity.LogProg.ISGen.gdouble_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Doubling the Code Bound

**Claim.** For every $m$ and register state with $e=m$, if all registers are bounded by $B$, $K2^m\le B$, and every stated counting-initialization run with code bound $K2^m$ terminates within the register bound and accepts exactly when $Q$ holds, then the doubling-state computation from that register state has the same termination, bound, and acceptance properties.

**Proof.** Proceed by induction on $m$, following the doubling program. When $m=0$, the test of $e$ takes the zero branch. The machine then enters the counting initialization with its existing $K,k,T$ values. These scratch values are at most $B$ by the register bounds, and $K2^0=K$, so the assumed counting-run property applies after identifying its initial state with the present one (`IG.of_eq`). The zero test is justified by `NSem.jz_pos`, with the register bound supplied by `St.greg`.

Now suppose $m$ is positive. The zero test takes its nonzero branch (`NSem.jz_neg`), and the program decrements $e$ (`nsem_dec`). It clears the scratch registers $T$ and $k$ (`NSem.clr`), then uses an add-twice loop to replace the old code bound $K$ by $2K$. The loop correctness theorem (`nsem_addTwice`) shows that the new value is exactly twice the old one; its side conditions follow from the register indices being distinct, from the current register bounds, and from the assumed bound $K2^{m+1}\le B$. The program clears $K$ and copies $T$ into it; the copy-loop theorem (`nsem_copy`) establishes this update while respecting the bounds. The register-state bound lemma (`St.greg`) supplies the guard at these intermediate program points.

The induction hypothesis now applies with exponent $m$: after decrementing $e$ and doubling $K$, the code bound is $2K$, which equals $K2^m$ for the original value at exponent $m+1$. The required inequality for the recursive call follows from $K2^m\le K2^{m+1}\le B$, and its initialization hypothesis is inherited from the assumed property for every scratch-register choice. The state identities used to align the recursive state with that hypothesis are arithmetic bookkeeping (`IG.of_eq`). Hence the doubling computation terminates within the bound and accepts exactly when $Q$ holds.

**Key facts.** `Complexity.LogProg.ISGen.St.greg`, `Complexity.LogProg.NSem.jz_pos`, `Complexity.LogProg.ISGen.IG.of_eq`, `Complexity.LogProg.NSem.jz_neg`, `Complexity.LogProg.nsem_dec`, `Complexity.LogProg.NSem.clr`, `Complexity.LogProg.nsem_addTwice`, `Complexity.LogProg.nsem_copy`.
