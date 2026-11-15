# Typed reduction advantage overlap disclosure

Worker: seq-zk-b. ReductionAdvantage.lean introduces no definitions or hosts. Searches are
retained in reduction-advantage-searches.log. Nearest generic readers are
EnsembleLemmas.acceptProb_coins_equiv and coinsEquiv/take_ofFn_coinsEquiv/
drop_ofFn_coinsEquiv (Asymptotic/EnsemblesLemmas.lean:85,141,151,156). They are directly reused,
not copied. This improves the initially proposed local splitCoins/cast equivalence by using
the already published exact split/cast constructor and its two tape readers.

CommitmentLemmas.acceptProb_distinguisherL_of_runAtL handles one deterministic preprocessor
with an equal coin polynomial. ThreeColoring/ColZKMachine.distAdv_distinguisherL_reparam
handles deterministic preprocessing with a changed security parameter. Neither handles the
random continuation suffix and independent final-distinguisher tape required here. Their
standard public-reader/reindexing pattern is reused, but no proof body was copied and no
new general probability transport theorem is introduced. The new theorem applies the
existing acceptance reindexer twice and the public distAdv_def.

Canonical FunFamily.blocks.symm only regroups the simulator coin table; its implementation
is not unfolded. The raw run equation is a hypothesis supplied by exists_phaseReduction,
so the proof does not unfold any foreign reduction or machine. Only the local equivalence
e is expanded. NUPPT.distinguisherL_eq/runAt_eq/coinLen_eq and PolyExpr evaluation readers
supply all foreign computations. No validity, reachability, witness or nonemptiness premise
was added. Parent approved this exact statement and source-only integration.
