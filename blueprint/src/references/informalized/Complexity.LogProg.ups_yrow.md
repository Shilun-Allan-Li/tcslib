<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathParse.lean :: Complexity.LogProg.ups_yrow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Row symmetry check

**Claim.** Under the stated register and address bounds, if adjacency is symmetric on every remaining row and every column, then the program at $s0$ with the row counter advanced to $\sigma.n$ has acceptance probability $q$; if the row-symmetry condition fails, $q=0$ implies the program at $y0$ has acceptance probability $q$.

**Proof.** We induct on $dd=\sigma.n-\sigma.u$. If $dd=0$, then $\sigma.u=\sigma.n$, so there are no rows left to check. The equality test therefore takes the continuation specified by the symmetry premise; the required reset-state continuation at $s0$ has probability $q$.

For the successor case, first advance the column-check routine from $y0$ to $y2$ with the column counter reset to zero. Apply the column-symmetry result (`ups_ycol`) to the current row. If its columns are symmetric, that routine advances to the next row and, by the row induction hypothesis, the remaining rows have probability $q$. The required symmetry premise for those rows follows by separating the current row from the later rows. If the column check fails, then the full row-symmetry condition fails as well, so the hypothesis gives $q=0$ and the rejecting branch has the required probability. The initial equality branch, register reset, and increment are then lifted through the program using their deterministic semantics.

**Key facts.** `Complexity.LogProg.PSem.jeq_pos`, `Complexity.LogProg.UPS.of_eq`, `Complexity.LogProg.UReg.reg`, `Complexity.LogProg.PSem.jeq_neg`, `Complexity.LogProg.PSem.clr`, `Complexity.LogProg.ups_ycol`, `Complexity.LogProg.PSem.inc`.
