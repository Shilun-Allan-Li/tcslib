<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.parseLit_repr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Representation of a Parsed Literal

**Claim.** If parsing $x$ returns literal $\ell=(v,b)$ and remainder $r$, then $x=1^{v+1}0b\,r$.

**Proof.** The true-run decomposition says that $x$ consists of as many initial true bits as the first component of the result of taking the initial true run, followed by the remaining list (Std.Sat.CNF.takeTrues_repr). In a successful literal parse, that run is nonempty and has length $v+1$; the remaining list starts with false and then the polarity bit $b$, followed by $r$. Substituting this parse result into the decomposition yields $x=1^{v+1}0b\,r$.

**Key facts.** `Std.Sat.CNF.takeTrues_repr`.
