<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean :: Complexity.ImplicitEnum.run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Enumerator Run

**Claim.** Under the stated bounds, the enumerator started in its initial configuration reaches a halted configuration with output $f(x)$ and work-tape head at zero, and all configurations at earlier times have the prescribed shape.

**Proof.** First identify the machine's initial configuration with the enumerator configuration that is asking, has empty output, and has counter zero. Apply the successive-rounds result (`rounds`) with $i=|f(x)|$. Its endpoint has output the first $|f(x)|$ bits of $f(x)$, hence output $f(x)$, and is asking with counter $|f(x)|$. Since the length oracle now answers negatively, one more step enters the halted state (`rstep_ask`). A further step from the halted state leaves the state, output, and head position as required: the halted state has no call and its ordinary transition halts without moving the work-tape head (`rstep_noncall`). Thus choose the total run length to be the rounds' length plus two, using the run-addition law (`rrun_add`) and the one-step run identity (`rrun_one`) to compose these transitions. For times before the rounds' endpoint, the shape bound comes from `rounds`. At the endpoint the machine is still asking, with counter $|f(x)|\le F$, so it satisfies the first clause of Shape. At the next time it is halted; this state has no call, and its work-tape head remains at zero, satisfying the second clause of Shape. The state field of each ordinary configuration is its named state stored as an option (`cfg_state`).

**Key facts.** `Complexity.ImplicitEnum.cfg_state`, `Complexity.ImplicitEnum.rounds`, `Complexity.ImplicitEnum.rstep_ask`, `Complexity.LogProg.rrun_add`, `Complexity.LogProg.rrun_one`, `Complexity.LogProg.rstep_noncall`.
