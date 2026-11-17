<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_copy_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copy Scan of a Captured Suffix

**Claim.** Starting at position $|pre|$ with `pre` followed by `old` on tape zero and `rest` on the last tape, the scan copies the image of `rest` under $f$ over the corresponding cells of tape zero, blanks the last tape, and enters $q_r$ after $|rest|+1$ steps, with both heads at $|pre|+|rest|-1$.

**Proof.** Proceed by induction on `rest`, generalizing `pre` and `old`. If `rest` is empty, the last tape is entirely blank. The machine therefore takes its blank-case transition: it makes no writes, moves both heads left, and enters $q_r$. The blank-prefix identity (`Complexity.enumCont_sparse_blanks`) identifies this tape content with the blank tape, and the resulting head position is $|pre|-1$, as claimed. For the inductive step, write `rest` as $b$ followed by a tail. The last-tape head reads $b$. The two-ended action law (`Complexity.enumCont_ends_apply`) describes this step: it writes $f(b)$ at the current cell of tape zero, blanks that cell on the last tape, moves both heads right, and leaves the machine in $q_c$. The overwrite identity (`Complexity.enumCont_overwrite`) records the updated tape-zero word; the sparse-tape clearing identity (`Complexity.enumCont_sparse_clear`) shows that the remaining tail is now positioned one cell farther along. Apply the induction hypothesis to that tail, with the prefix extended by $f(b)$ and the old suffix correspondingly advanced. The first step plus the tail scan takes $|rest|+1$ steps; the resulting word, blank last tape, state, and head position are exactly those asserted.

**Key facts.** `Complexity.enumCont_sparse_blanks`, `Complexity.enumCont_ends_apply`, `Complexity.enumCont_overwrite`, `Complexity.enumCont_sparse_clear`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
