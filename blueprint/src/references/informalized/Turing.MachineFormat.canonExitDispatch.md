<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonExitDispatch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dispatching an Exit State

**Claim.** A machine can be built that simulates the given machine until its first visit to an exit state, then takes one additional step into a distinct label recording the verdict bit, without reaching any such label earlier.

**Proof.** Use a two-phase state space: phase $0$ carries a state of the original machine, and phase $1$ carries an optional Boolean value. In phase $0$, simulate the original machine. Define the redirect map so that a state equal to one of the three exit states—corresponding to no bit, $0$, or $1$—redirects to phase $1$ carrying respectively $0$, $0$, or $1$; all other states have no redirect. The injectivity of the given exit map ensures these tests identify the intended cases. The phase-host simulation theorem (`phaseHostTM_run`) says that, provided no redirect is enabled during the first $t$ steps, the new machine agrees with the original simulation through time $t$, then reaches the redirected state at time $t+1$. The hypothesis excluding earlier visits to any exit state makes every redirect disabled at each time $u<t$. At time $t$, the reached exit state redirects to the label selected by whether $v$ is the present bit $1$. Finally, before that last step all simulated states have phase $0$, whereas every label has phase $1$; the two phases are disjoint, so no label is reached at any time through $t+1$ before the redirected configuration.

**Key facts.** `Turing.phaseHostTM_run`.
