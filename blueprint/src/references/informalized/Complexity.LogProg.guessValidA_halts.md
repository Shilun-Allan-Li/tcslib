<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMExample.lean :: Complexity.LogProg.guessValidA_halts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting of the valid-input checker

**Claim.** For every input, predicate on configurations, and oracle with no query indices, if the predicate holds at all four states with zero register and arbitrary answer component, then every three-bit choice sequence halts after three steps and satisfies the predicate at every earlier active configuration.

**Proof.** First consider the two deterministic branches after the initial choice. From the validation state, the validity instruction either advances to the final state or halts immediately with a negative answer. In the advancing case, the return-true instruction halts on the next step. The deterministic halting principle (`NHalts.det`), together with the assumed predicate at the active states, combines these possibilities into a two-step halting result for this branch. From the other branch, the return-false instruction halts in one step; the same principle gives its two-step halting result. The halted-run principle (`NHalts.halted`) supplies the residual steps once a branch has halted. Finally, the choice halting principle (`NHalts.choose`) joins the two branches and accounts for the initial choice step. Its predicate hypothesis is precisely the assumed predicate at the initial state, and the resulting run halts after three steps while satisfying the predicate at every earlier active configuration.

**Key facts.** `Complexity.LogProg.NHalts.det`, `Complexity.LogProg.NHalts.halted`, `Complexity.LogProg.NHalts.choose`.
