<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clVisitRows_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time visit table

**Claim.** For every finite-state binary Turing machine $M$ and natural numbers $C,e,c,A,d$, the function sending $x$ to the visit table with the stated count is polynomial-time computable.

**Proof.** Choose a machine $W$ that implements one producer step by a clean call: for every input and argument it reaches a designated exit configuration in polynomial time, without reaching that exit earlier ($\texttt{Complexity.clVisitStep\_cleanCall}$). Let $N(x)$ be the requested number of rows, and start from the encoded state containing $x$, time zero, and an empty table. This initial state is polynomial-time computable by pairing the identity function with a constant function. The unary clock of length $N(x)$ is also polynomial-time computable ($\texttt{Complexity.clProducerClock\_native}$). The repeat-argument construction packages the initial state and this clock into the input for the repeated computation, and is polynomial-time computable ($\texttt{Complexity.clRepeatArgument\_native}$).

For that packaged input, let $L$ be its length. The width bounds for packed fields show that both $N(x)$ and $|x|$ are at most $L$. The retained-state estimate then bounds the length of every intermediate state through the first $N(x)$ iterations by $(8+8k)(L+1)^2$ ($\texttt{Complexity.clVisitState\_size}$). The clean-call result lets the repeat-output machine carry out each producer step; the retained-state bound supplies its required uniform width bound. The repeat-budget estimate converts the sum of the input, simulation, and iteration costs into a polynomial in $L$. Thus the repeated computation is polynomial-time, and the orbit identity identifies its result with the state containing the first $N(x)$ visit rows ($\texttt{Complexity.clVisitStep\_orbit}$). Finally, decoding the appropriate header tail extracts the table and is polynomial-time ($\texttt{Complexity.clHeaderTail\_native}$); composition gives the desired polynomial-time function.

**Key facts.** `Complexity.clVisitStep_cleanCall`, `Complexity.polyTimeComputable_id`, `Complexity.clNative_pair`, `Turing.FinTM.computesFunInTime_const`, `Complexity.clProducerClock_native`, `Complexity.clRepeatArgument_native`, `Complexity.clFields_width`, `Complexity.clVisitState_size`, `Complexity.clRepeatOutput_compute`, `Complexity.clVisitStep_orbit`, `Complexity.clRepeat_budget`, `Complexity.clHeaderTail_native`, `Complexity.PolyTimeComputable.comp`.
