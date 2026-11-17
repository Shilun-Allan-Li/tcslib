<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.parseLit_serializeLit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Literal Encoding Round Trip

**Claim.** For any literal $\ell=(v,b)$ and bit string $r$, parsing $1^{v+1}0b\,r$ returns $\ell$ and remainder $r$.

**Proof.** The encoding begins with exactly $v+1$ true bits, followed by false and then $b$. The initial-true-run parser therefore returns that run length and leaves the false bit, $b$, and $r$ intact (Std.Sat.CNF.takeTrues_replicate). The literal parser reads the positive run as variable index $v$, consumes the false separator and polarity bit $b$, and leaves precisely $r$.

**Key facts.** `Std.Sat.CNF.takeTrues_replicate`.
