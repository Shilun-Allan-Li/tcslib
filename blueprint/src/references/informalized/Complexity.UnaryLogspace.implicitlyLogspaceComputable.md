<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean :: Complexity.UnaryLogspace.implicitlyLogspaceComputable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Logspace Gives Implicit Computability

**Claim.** If both unary index languages for $g$ are in logarithmic space and the lengths of $g(n)$ have a polynomial bound, then the extension that returns $g(n)$ on unary inputs and the empty string otherwise is implicitly logspace computable.

**Proof.** Choose constants $C,c$ witnessing the polynomial output-length bound. The extension’s output is either $g(|x|)$, when $x$ is unary, or empty, so its length is bounded by $C(|x|+1)^c$ (the empty case satisfies the bound as well). For either index predicate—bit membership or being below the output length—the proof observes that the predicate for the extended function holds exactly when $x$ is unary and the corresponding predicate for $g(|x|)$ holds. On unary inputs that predicate is precisely the defining predicate of the associated unary language. The identity converting such unary-input index languages to ordinary index languages (`Complexity.indexLang_unaryExt`) therefore identifies the extension’s bit and length languages with the given languages for $g$. Both are in logarithmic space by hypothesis, proving all three requirements of implicit logspace computability.

**Key facts.** `Complexity.indexLang_unaryExt`.
