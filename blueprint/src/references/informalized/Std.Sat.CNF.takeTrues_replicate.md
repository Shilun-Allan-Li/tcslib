<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.takeTrues_replicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leading Run of a Unary Block

**Claim.** For every natural number $k$ and bit string $r$, removing the longest initial run of ones from $1^{k+1}0r$ returns run length $k+1$ and remainder $0r$.

**Proof.** Induct on $k$. When $k=0$, the input begins with a single $1$ followed by $0r$, so the defining recursion returns run length one and remainder $0r$. For the successor case, separate the first $1$ from the block of remaining ones. By the induction hypothesis, removing the run from that remaining block followed by $0r$ returns length $k+1$ and remainder $0r$. The defining recursion adds one to this run length and preserves the remainder, giving $k+2$ and $0r$, as required.
