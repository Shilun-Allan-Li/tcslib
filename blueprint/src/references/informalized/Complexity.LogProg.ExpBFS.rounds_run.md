<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Search.lean :: Complexity.LogProg.ExpBFS.rounds_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Closure After a Relaxation Round

**Claim.** A relaxation round preserves marked cells and confines changes to the designated block. Every predicate preserved by true step edges and true of the initially marked indices remains true of every marked index afterward; the final marked set is also closed under the step relation within the block.

**Proof.** Induct by strong induction on the number $j$ of initially unmarked cells in the block. First, two deterministic steps reset $U$ and the change flag to zero. From this configuration the outer-round theorem (`outer_run`) scans the block. It yields a memory $M_1$ that extends $M$, differs only inside the block, and satisfies the predicate-preservation conclusion. It also supplies a flag $c_1$ with the dichotomy that no memory change leaves the flag zero, while a change sets it to one. If $M_1=M$, the flag is zero. The machine proceeds directly to the count control, and the desired final closure property follows from the outer-round conclusion for edges out of initially marked sources; together with the unchanged memory, this is closure of the marked set. If $M_1\ne M$, the flag is one. Since the memory only gains marks and changes only within the finite block, at least one formerly unmarked cell has become marked. Therefore the number of unmarked cells strictly decreases (`unmarked_lt`), so the induction hypothesis applies to a second round starting with $U=K$ and flag one. That round retains monotonicity and confinement, and its predicate-preservation statement composes with the first round's statement. Its closure conclusion gives closure under every true edge within the block for the resulting memory. The two guarded runs are concatenated, and the counters and bounds needed to maintain the guard are preserved throughout.

**Key facts.** `Complexity.LogProg.ExpBFS.outer_run`, `Complexity.LogProg.ExpBFS.unmarked_lt`, `Complexity.LogProg.ExpBFS.Mono.refl`, `Complexity.LogProg.ExpBFS.Mono.trans`, `Complexity.LogProg.ExpBFS.Out.refl`, `Complexity.LogProg.ExpBFS.Out.trans`, `Complexity.LogProg.ExpBFS.cont`, `Complexity.LogProg.ExpBFS.ex1_pre`, `Complexity.LogProg.ExpBFS.reach_cf`, `Complexity.LogProg.ExpBFS.step_of`, `Complexity.LogProg.MReach.refl`.

**Caveat.** The account relies on the detailed behavioral conclusions of `outer_run`, whose proof is not available in this request; the derivation of strict decrease also uses the supplied `unmarked_lt` lemma.
