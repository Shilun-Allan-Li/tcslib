<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Transducer.lean :: Complexity.polyTimeComputable_transduce -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Transducer Computation

**Claim.** For a finite state set, a transition function, an emission function, and a chosen initial state, the function that processes each input bit from left to right, emits its associated bit when present, and updates the state is polynomial-time computable.

**Proof.** A deterministic transducer machine is built from the transition and emission functions and the chosen initial state. Its computation theorem says that on every input of length $n$ it produces exactly the recursively specified transduction and halts within $n+1$ steps (`transducerTM_computes`). This is a linear time bound, so the general result that a function computed in linear time is polynomial-time computable applies (`polyTimeComputable_of_linear`).

**Key facts.** `Complexity.transducerTM_computes`, `Complexity.polyTimeComputable_of_linear`.
