<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.exists_maskSelect_host -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nondeterministic host for masked selection

**Claim.** For every language V in P and natural numbers C,c, there are polynomial bounds and a nondeterministic machine whose choices determine a subsequence selected by a mask with exactly C(|x|+1)^c selected positions, and whose output indicates whether x followed by that subsequence belongs to V.

**Proof.** Choose a deterministic polynomial-time decider for V, with running-time bound A(n+1)^d. Also choose a machine S that, on unary input of length n, outputs a string of C(n+1)^c true bits in polynomial time. The unary-input conversion gives a time τ(n) for S on arbitrary inputs of length n: it produces the same output, halts at time τ(n), and remains active before then; moreover τ(n) is bounded by the unary running-time bound. (These facts come from `mem_P_iff`, `computesFunInTime_polyUnary`, and `b2_unary_first`.)

Fix x, let T=τ(|x|), and form the emission mask recording which of the T steps of the unary computation output a bit. Its length is T, and its number of true entries is Q=C(|x|+1)^c: the output of S consists of exactly Q true bits, as certified by `cont_mask_count` and the computation’s output. The mask selects from the first T nondeterministic choice bits exactly the bits emitted by S; `contSelect_eq_maskSelect` identifies this continuous selection with the stated masked selection.

The host machine first uses 2|x|+2 choices to initialize its simulation and then simulates S for T steps, using the next T choices as the guessed word g. Since the simulated computation stays active until time T, `b2_guess_run` says the host reaches the configuration containing the selected string. It then runs the decider for V on x concatenated with that string. The selected string has length Q, so this final computation fits the decider’s bound at input length |x|+Q; `b2_finish` therefore guarantees that the host halts and outputs the membership indicator for every remaining choice suffix of the required length.

Set s=2|x|+2 and take the mask just constructed. The total choice budget H=2|x|+2+T+B_v, where B_v is the final-decider allowance, is bounded by a polynomial in |x|: `b2_host_bound` combines the unary simulation and decider bounds, and `cont_guess_time_bound` puts that polynomial into the requested form K(|x|^e+1). Choose K and e as in the proof. Any longer choice string has the same run as its prefix of length H, because the host has already halted; `runWith_append` decomposes the run into prefix and suffix, and `runWith_of_halt` shows the suffix has no effect. The selected prefix bits are exactly the corresponding initial bits of the full choice string, proving the required output formula and length bound.

**Key facts.** `Complexity.mem_P_iff`, `Turing.FinTM.computesFunInTime_polyUnary`, `Complexity.b2_unary_first`, `Complexity.cont_mask_length`, `Complexity.cont_mask_count`, `Complexity.contSelect_eq_maskSelect`, `Complexity.b2_guess_run`, `Complexity.b2_host_bound`, `Complexity.cont_guess_time_bound`, `Complexity.b2_start`, `Complexity.b2_finish`, `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt`.
