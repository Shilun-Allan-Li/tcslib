<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean :: Complexity.LogProg.MHalt.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of guarded halting

**Claim.** If the machine halts with answer $r$ after finitely many steps while $G$ holds at every earlier configuration, and $G$ implies $G'$, then it also halts with answer $r$ while $G'$ holds at every earlier configuration.

**Proof.** Take a halting time $T$ witnessing the hypothesis. Keep the same time and the same two endpoint facts: the run is halted at $T$ and has answer $r$. For any time $t<T$, the original invariant gives $G$ at the configuration reached at time $t$, and the implication $G\Rightarrow G'$ therefore gives $G'$ there. Thus $T$ also witnesses the desired guarded halting.
