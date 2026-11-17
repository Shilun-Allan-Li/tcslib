<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean :: Complexity.LogProg.ExpBFS.ini_orcN -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Code Oracle Characterization

**Claim.** For a finite nondeterministic Turing machine $N$, bit string $x$, and natural numbers $r,u$, the initial-code oracle accepts the paired input encoding $x$, $u$, and $r$ exactly when $u$ is the code of the initial configuration of $N$ on $x$ with window parameter $r$.

**Proof.** The membership characterization of the machine's initial-configuration language says that this paired encoding belongs to that language exactly when the initial configuration code at window parameter $r$ equals $u$ (`Complexity.Codec.mem_initLang`). By definition, the oracle is the Boolean indicator of the corresponding language among the four deciders; the indicator equals the decision of language membership (`Complexity.LogProg.indicator_eq_decide`). Substituting the paired encoding into these two facts identifies oracle acceptance with the stated code equality.

**Key facts.** `Complexity.Codec.mem_initLang`, `Complexity.LogProg.indicator_eq_decide`.
