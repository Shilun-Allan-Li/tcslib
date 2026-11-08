<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDHost.lean :: Turing.NDTM.phaseHostND_fixChoice -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Choice and Phase Hosting

**Claim.** Fixing choice $b$ in the phase-hosted nondeterministic machine gives exactly the same deterministic machine as first fixing choice $b$ in each phase machine and then phase-hosting them.

**Proof.** Both machines have initial state $q_0$. At a state tagged by phase $i$, each transition first checks the same redirection value: if redirection is present, both machines make the same redirection transition; if it is absent, both use the transition of $M_i$ at choice $b$, with its successor state tagged by $i$. Thus the initial states and transition functions agree by their definitions, so the machines are equal.
