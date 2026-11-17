<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean :: Complexity.LogProg.SavitchARM.mem_iff_reach -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership and bounded reachability

**Claim.** Under the space, width, and configuration-bound hypotheses, $x$ belongs to $L$ exactly when there are codes below $2^w$ for an initial and an accepting configuration, with the accepting code reachable from the initial code at depth $w$.

**Proof.** For the forward implication, membership yields a finite code chain from an initial configuration code to an accepting configuration code, by `mem_iff_codeChain` (the language-membership characterization by a bounded code chain). Its length is at most the configuration bound, and every code in the chain is below $2^{	ext{codeK}(N)(s+	ext{logSpace}(|x|)+1)}$. The width hypothesis places this exponent below $w$, so monotonicity of powers of $2$ gives the stronger bound $2^w$ for each code. Apply `reach_of_chain` (a chain of length at most $2^w$ yields a reachability witness at depth $w$) to the chain, using the code bounds; this gives the desired bounded-depth reachability between its first and last codes. These endpoints have the required initial and accepting encodings. Conversely, bounded reachability implies a reflexive-transitive path of one-step configuration relations by `reflTransGen_of_reach`. The initial encoding, that path, and the accepting encoding then imply membership by `mem_of_codePath` (the code-path characterization of membership).

**Key facts.** `Complexity.Codec.mem_iff_codeChain`, `Complexity.LogProg.SavitchARM.reach_of_chain`, `Complexity.LogProg.SavitchARM.reflTransGen_of_reach`, `Complexity.Codec.mem_of_codePath`.
