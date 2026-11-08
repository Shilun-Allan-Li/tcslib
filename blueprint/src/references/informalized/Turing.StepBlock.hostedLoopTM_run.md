<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlockLoop.lean :: Turing.StepBlock.hostedLoopTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hosted Bounded-Loop Simulation

**Claim.** The hosted machine simulates the bounded loop for the prescribed number of steps, with the stated time bounds, representation and tape-frame properties, and virtual boundary tag. It reaches the appropriate completed-loop or escape anchor at time $T$, and neither anchor occurs earlier.

**Proof.** Apply the bounded-loop simulation theorem (`loopTM_run`) to obtain a time $T$, simulated configuration $e$, and tape content $ct'$, together with the time bounds, representation, output preservation, tape-frame property, and the unhosted loop's endpoint and earlier-time exclusion. To host this run, first observe that the starting loop configuration has the same input position as $d$: this follows from the input-position clause of the representation relation. Thus the given virtual boundary tag for $c$ is also valid for the loop configuration built from $d$. The virtual-host simulation theorem (`vhostEmitTM_runFrom`) now supplies a tag $b'$ and identifies the hosted run at time $T$ with the virtual-host configuration over the unhosted endpoint. Substituting the endpoint supplied by `loopTM_run` gives the required hosted endpoint and preserves the established bounds and representation properties. Finally, fix any $u<T$. Apply the virtual-host simulation theorem again at time $u$ to express the hosted configuration as a virtual hosting of the unhosted loop configuration at that time. If its state were either hosted exit anchor, projecting its state to the unhosted loop-control component would make the unhosted state the corresponding exit anchor. This contradicts the earlier-time exclusion from `loopTM_run`, proving that neither hosted anchor occurs before $T$.

**Key facts.** `Turing.StepBlock.loopTM_run`, `Turing.vhostEmitTM_runFrom`.
