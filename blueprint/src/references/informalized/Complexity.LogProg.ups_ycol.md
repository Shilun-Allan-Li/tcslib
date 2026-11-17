<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathParse.lean :: Complexity.LogProg.ups_ycol -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Column symmetry check

**Claim.** Under the register and address bounds, if adjacency is symmetric across every remaining column in row $\sigma.u$, then each continuation from the end of that row has acceptance probability $q$; if any such symmetry check fails, $q=0$ implies the program at $y2$ has acceptance probability $q$.

**Proof.** We induct on $dd=\sigma.n-\sigma.w$, the number of columns remaining. If $dd=0$, then $\sigma.w=\sigma.n$. The symmetry condition over columns from $\sigma.w$ onward is vacuous, so the assumed continuation at $yn$ applies; the equality test recognizes this endpoint and reaches that continuation with the registers in the required state.

For the successor case, the current column satisfies $\sigma.w<\sigma.n$. The program uses `ups_index` to position the input pointer at the encoded edge in row $\sigma.u$, column $\sigma.w$, and at the reverse edge in row $\sigma.w$, column $\sigma.u$. It queries the two edge bits. If they agree, the column-symmetry condition holds at this column, and incrementing $w$ reduces the remaining-column count by one. The induction hypothesis then applies: its symmetry premise is obtained by combining the current equality with the original premise for all later columns, and its failure premise follows from the original failure condition. If the two bits disagree, the symmetry condition for the full remaining range is false. The corresponding branch rejects, and the hypothesis that failure forces $q=0$ makes this rejection have the required probability. In both orientations of disagreement, the call answers select the rejecting branch; the call and equality-test semantic rules lift these conclusions back to $y2$.

**Key facts.** `Complexity.LogProg.PSem.jeq_pos`, `Complexity.LogProg.UPS.of_eq`, `Complexity.LogProg.UReg.reg`, `Complexity.LogProg.ups_index`, `Complexity.LogProg.PSem.inc`, `Complexity.LogProg.PSem.call_pos`, `Complexity.LogProg.PSem.call_neg`, `Complexity.LogProg.ups_rej`, `Complexity.LogProg.PSem.jeq_neg`, `Complexity.LogProg.UReg.v_0`, `Complexity.LogProg.UReg.v_11`, `Complexity.LogProg.UReg.v_12`, `Complexity.LogProg.pathOr_bit`, `Complexity.rowMajor_lt`.
