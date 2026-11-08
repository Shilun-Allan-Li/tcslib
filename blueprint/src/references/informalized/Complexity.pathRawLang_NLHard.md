<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardDecide.lean :: Complexity.pathRawLang_NLHard -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NL-hardness of the raw path language

**Claim.** Every language in nondeterministic logarithmic space has a logspace many-one reduction to the raw path language.

**Proof.** Membership of $L$ in NL provides a constant $c_0$ and a nondeterministic machine $N$ deciding $L$ within the corresponding logarithmic-space bound. Apply the established path reduction for $N$ and $c_0$. Its output map is implicitly logspace-computable (`Complexity.PathHard.implicitlyLogspaceComputable_red`), and the reduction correctness theorem says that an input belongs to $L$ exactly when its image belongs to the raw path language (`Complexity.PathHard.red_mem_iff`). These are precisely the computability and membership conditions for the required many-one reduction.

**Key facts.** `Complexity.PathHard.implicitlyLogspaceComputable_red`, `Complexity.PathHard.red_mem_iff`.
