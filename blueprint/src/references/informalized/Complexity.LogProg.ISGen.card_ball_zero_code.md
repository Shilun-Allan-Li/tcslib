<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean :: Complexity.LogProg.ISGen.card_ball_zero_code -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ball Cardinality at Zero Code

**Claim.** Under the stated exponential bound on $K$, the $K$-bounded ball at level zero has cardinality one.

**Proof.** Let $u_0$ be the code of the initial configuration. The code-length estimate (`cfgCode_lt`) places $u_0$ below the exponential bound, and hence below $K$. The initial-code characterization (`mem_initLang`) says that a number satisfies the initial predicate exactly when it equals $u_0$: membership of the encoded input in the initial language is equivalent to its code being the initial configuration code. The zero-level ball cardinality result (`card_ball_zero`) applies when the distinguished initial code lies below $K$ and the initial predicate characterizes exactly that code. It therefore gives cardinality one.

**Key facts.** `Complexity.Codec.cfgCode_lt`, `Complexity.Codec.mem_initLang`, `Complexity.LogProg.ISCount.card_ball_zero`.
