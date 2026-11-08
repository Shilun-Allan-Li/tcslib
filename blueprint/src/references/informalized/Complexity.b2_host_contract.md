<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_host_contract -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Host Contract for Extracted Words

**Claim.** For the specified computation of $v$ by the normalized scheduler and the time-bounded decision procedure for $V$, every choice word of the prescribed length makes the host halt with the indicator of $x+u\in V$ for some $u$ of length $|v|$; conversely, each such $u$ is realized by a choice word of that length.

**Proof.** Let $c$ be the scheduler's configuration after $T$ steps, and let $B=|x|+|v|+2+(A(|x|+|v|+1)^d+1)$. The computation hypothesis gives that $c$ is halted and has output $v$ (`computesInTime_iff`). The guessing-coverage result says that every length-$T$ choice segment reaches this same scheduler configuration with some guessed word $u$ of length $|v|$, and that every such $u$ can be obtained from some length-$T$ segment (`b2_guess_coverage`). Once at this configuration, the finishing result says that every length-$B$ suffix makes the host halt with the indicator of $x+u\in V$ (`b2_finish`), using the decision procedure's time bound. The host's initial loading segment of length $2|x|+2$ reaches the initial guessing configuration (`b2_start`).

For the forward direction, split an arbitrary choice word of total length $2|x|+2+T+B$ into a prefix $a$ of length $2|x|+2$, a middle segment $g$ of length $T$, and a suffix $z$ of length $B$. The prefix and middle segments put the host into the guessing configuration with some $u$ of length $|v|$; the finishing result then gives the required halted configuration and output. The decomposition is a consequence of the list take-and-drop identities, and the run over concatenated segments is evaluated successively by `runWith_append`.

For the converse, choose a length-$T$ segment $g$ that realizes the prescribed $u$, as guaranteed by coverage. Pad it with an arbitrary prefix of length $2|x|+2$ and suffix of length $B$ (for example, all-false words). The same startup and finishing arguments give the required outcome, and the concatenated choice word has the prescribed total length.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Complexity.b2_guess_coverage`, `Complexity.b2_start`, `Complexity.b2_finish`, `Turing.NDTM.runWith_append`.
