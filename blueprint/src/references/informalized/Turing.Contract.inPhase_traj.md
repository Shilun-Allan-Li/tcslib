<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean :: Turing.Contract.inPhase_traj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trajectory Through a Phase Host

**Claim.** Up to and including the specified duration, the host run agrees with the phase-$p$ run on the projected configuration, with states mapped into phase $p$. One step later it is the contract endpoint with its state bound through the reduction map, and that endpoint state belongs to $X$.

**Proof.** 1. Let $c$ be the phase-$p$ projection of the initial host configuration $d$. Since $d$ starts in state $(p,s_0)$, mapping the state of $c$ back into phase $p$ recovers $d$; all other configuration data are unchanged. Also, $c$ starts in state $s_0$ and satisfies the precondition of $C$.

2. The contract’s endpoint condition puts the state of $C$’s endpoint in $X$. It cannot be halted, because the halted state is excluded from $X$. Thus the endpoint state is some $s'$, and $s'\in X$. By the phase-reduction hypothesis, there is a host state $q'$ in a different phase to which $s'$ reduces.

3. The phase-host trajectory theorem (`Turing.phaseHostTM_run`) applies to the run of $M_p$ from $c$: before the endpoint, the reduction map is inactive. Indeed, at each earlier time the contract’s cut condition excludes states in $X$, so the reduction hypothesis sends each such state to no successor. The theorem therefore identifies the host run with the phase-$p$ run through time $C$’s duration, and identifies the next host configuration with the endpoint relabeled to $q'$. At that endpoint, the relabeling by $q'$ agrees with binding the endpoint’s optional state through the reduction map: its state is $s'$, and the reduction sends $s'$ to $q'$. These give the stated trajectory and endpoint equalities, together with $s'\in X$.

**Key facts.** `Turing.phaseHostTM_run`.
