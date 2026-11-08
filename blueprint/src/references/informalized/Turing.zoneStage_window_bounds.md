<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneStage_window_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zone Window Bounds

**Claim.** If $-1\le p\le 2$ times the capacity of zone $i$, then both indicated left and right window cells lie between $-(2b_{i+1}+2)$ and $2b_{i+1}+2$.

**Proof.** The base at the next zone is the current base plus the current zone capacity (`zoneBase_succ`). Substituting $b_{i+1}=b_i+\mathrm{capacity}(i)$, the assumed lower and upper bounds on $p$ give the required lower and upper bounds for each of the two displayed expressions by rearranging the inequalities.

**Key facts.** `Turing.zoneBase_succ`.
