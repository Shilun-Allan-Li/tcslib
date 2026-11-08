<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputDevice.lean :: Turing.nativeAt_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial input head position

**Claim.** For every natural number $K$, state set $S$, symbol alphabet $\Gamma$, starting state $q_0\in S$, and input word $y\in\Gamma^*$, the initial configuration on $y$ has its input head at position $1$.

**Proof.** By definition, the initial configuration on $y$ assigns the input head position $1$. The predicate in question asserts exactly that this position equals $1$, so the claim follows by reflexivity.
