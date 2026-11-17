<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathSearch.lean :: Complexity.LogProg.ups_ssearch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Candidate Search Invariant

**Claim.** Under the stated register bounds and pattern hypotheses, the search-loop configuration in state $s1$ has acceptance probability $q$ and satisfies the program’s termination and register-bound conditions.

**Proof.** Proceed by induction on the remaining number $dd=\sigma.n-\sigma.u$ of candidates. If $dd=0$, then $\sigma.u=\sigma.n$, so there is no candidate in the search interval. The hypothesis for an empty search therefore gives $q=0$. The program’s equality test takes its positive branch, which rejects; the rejection state has probability zero, establishing the claim. This uses the deterministic equality-branch rule (`PSem.jeq_pos`) and the zero-probability semantics of rejection (`ups_rej`).

For the successor case, $\sigma.u<\sigma.n$. The equality test takes its negative branch. The program clears the scratch register and copies the saved input pointer into it, using the copy routines summarized by `ups_cp`. It then compares the doubled encoding of the current candidate $\sigma.u$ at pointer $\sigma.q$. If that pattern occurs, the comparison routine advances to the corresponding candidate-processing configuration; its semantics with probability $q$ follow from the assumed candidate hypothesis. If the pattern does not occur, the routine advances the candidate counter and returns to the search stage. The remaining interval has one fewer candidate, so the induction hypothesis applies. Its empty-search premise follows because any matching candidate in the old interval is either the just-tested candidate, which the failed comparison rules out, or lies in the shortened interval. The comparison routine’s two cases are supplied by `ups_scmp`; clearing and incrementing the relevant registers preserve the semantics by `PSem.clr` and `PSem.inc`. The bound $\operatorname{length}(\mathrm{bits}(\sigma.u))\le \sigma.u$ ensures the pointer used by the comparison remains within the available register bound.

**Key facts.** `Complexity.LogProg.PSem.jeq_pos`, `Complexity.LogProg.ups_rej`, `Complexity.LogProg.ups_cp`, `Complexity.LogProg.ups_scmp`, `Complexity.LogProg.PSem.clr`, `Complexity.LogProg.PSem.inc`, `Turing.length_bits_le_self`.
