<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.parseLit_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Consumed by Literal Parsing

**Claim.** If parsing $x$ as a literal returns $\ell=(v,b)$ and remainder $r$, then $v+3+|r|=|x|$.

**Proof.** The length identity for the initial run of true bits states that the number of such bits plus the length of what remains is exactly $|x|$ (Std.Sat.CNF.takeTrues_length). A successful literal parse must have a positive run, followed by false, then the polarity bit $b$, with remainder $r$. Thus the run has length $v+1$, and the two intervening bits contribute two more positions. Hence $|x|=(v+1)+2+|r|=v+3+|r|$.

**Key facts.** `Std.Sat.CNF.takeTrues_length`.
