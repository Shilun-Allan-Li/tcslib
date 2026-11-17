<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitSolve_of_body -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Split Solver Construction

**Claim.** Under the stated start and round assumptions for the body machine, there is a finite Boolean Turing machine that computes the encoded split of each input according to the equation $i+C(i+1)^e=|w|$, returning the empty word when no such $i$ exists. Its running time is bounded by a constant times $(|w|+1)^{e+2}$, and its space at every time is bounded by a constant times $(|x|+1)^{e+1}$.

**Proof.** The proof builds the solver by repeatedly running the body machine, maintaining a candidate word $s$ on its work tape. It first obtains a machine that computes the binary expansion of the input length in linear time and uses at most a linear amount of space, up to a fixed constant (the length-bits machine, `computesFunInTime_lengthBits_spaceUsed`). Since $n+1\le (n+1)^{e+1}$, its running-time bound can be enlarged so that computing the bits of $|w|$ takes at most $(A+a)(|w|+1)^{e+1}$ steps, where $a$ is the constant from that machine.

It then applies the loop construction (`f2_exists_loopFind_space`) with initial candidate the empty word, update rule that appends true when $|s|\le |w|$ and otherwise leaves $s$ unchanged, and acceptance test $|s|+C(|s|+1)^e=|w|$. The invariant is $|s|\le |w|+1$: it holds initially and is preserved by each update (`f2_splitStep_inv`). The start assumption ensures the body machine reaches the anchor state with the empty candidate within the enlarged time bound. The round assumption ensures each iteration from the anchor either halts with the correctly encoded prefix and suffix when the acceptance equation holds, or returns to the anchor with the updated candidate; its positive-time and intermediate-state conditions are precisely what lets the loop construction identify and count successive rounds.

The loop construction therefore gives a machine computing the loop's output, with its general time bound. The output is exactly the desired split: after $i$ updates the candidate has length $i$ until the bounded search range is exhausted, and the loop's acceptance test is the equation used by `solveSplit`. The explicit identification of these two outputs is supplied by the split-loop result lemma (`f2_splitLoop_result`). Applying the monotonicity of computation time (`ComputesInTime.mono`) to the loop's bound and the split-loop polynomial estimate (`f2_splitLoop_bound`) yields a bound of the form $2c(A+a+1)(|w|+1)^{e+2}$.

Finally, the loop construction bounds space at every time by $c((A+a)(|x|+1)^{e+1}+1)$. Because $(|x|+1)^{e+1}\ge1$, the quantity in parentheses is at most $(A+a+1)(|x|+1)^{e+1}$. Enlarging the constant once more gives the claimed space bound with the same final constant used for time.

**Key facts.** `Turing.FinTM.computesFunInTime_lengthBits_spaceUsed`, `Turing.FinTM.f2_exists_loopFind_space`, `Turing.FinTM.f2_splitStep_inv`, `Turing.FinTM.f2_splitLoop_result`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.f2_splitLoop_bound`.
