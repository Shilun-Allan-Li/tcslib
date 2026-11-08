<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassOracle/Classes.lean :: Complexity.POracle_subset_NPOracle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Oracle Time Is Nondeterministic Oracle Time

**Claim.** For every Boolean oracle language $O$, every language decidable in polynomial time by a deterministic oracle machine is decidable in polynomial time by a nondeterministic oracle machine with the same oracle; thus $\mathrm{P}^O\subseteq\mathrm{NP}^O$.

**Proof.** Take $L\in\mathrm{P}^O$, witnessed by a deterministic oracle machine $M$ running within $c(n^e+1)$ steps. Regard $M$ as a nondeterministic oracle machine whose transition ignores the choice bit. Its run is therefore the same for every choice string: the simulation identity \texttt{Turing.OracleTM.toOracleNDTM_runWith} identifies a run on a choice string $w$ with the deterministic run for $|w|$ steps. The nondeterministic machine is required to halt on every choice string of the prescribed length, and this identity transfers the deterministic halting guarantee to each such branch. If $x\in L$, choose the all-false choice string of length $c(|x|^e+1)$; its run is the deterministic accepting run, so the nondeterministic machine accepts. Conversely, if any branch accepts, the same identity shows that the deterministic run has the output prescribed by its decider. Since that output is the indicator of membership in $L$, acceptance implies $x\in L$. Thus the nondeterministic machine decides $L$ within the same polynomial bound.

**Key facts.** `Turing.OracleTM.toOracleNDTM_runWith`.
