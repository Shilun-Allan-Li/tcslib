<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Turing.FinNDTM.AbortDecidesInTime.restart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness and Expected Time of Restart

**Claim.** For each fixed input, repeatedly running the machine in blocks of the prescribed length has expected number of choices at most twice that block length, and any bit it returns is the correct membership indicator.

**Proof.** Fix $x$ and write $t=T(|x|)$ and $\ell$ for the membership indicator. First, $t>0$: if $t=0$, the halting guarantee applied to the empty choice word would say that the initial configuration is halted, whereas its state is the machine’s initial state. A single block fails to return a bit only when its output is not a one-bit string. In particular, this failure event is contained in the event that the output is not $[\ell]$. Since the probability of outputting $[\ell]$ is at least $1/2$, the probability of failure is at most $1/2$. The restart expected-time bound for independent blocks with failure probability at most $1/2$ now gives the bound $2t$ (the restart estimate `Randomized.expTimeLe_repeatRun`).

If the restart procedure returns $b$, some block $u$ of length $t$ must have returned that bit. Thus the machine’s output on $u$ is $[b]$. The aborting-decision condition rules out output $[\ell]$, so $b\ne\ell$. Since both are Boolean values, $b$ is the opposite bit, which is the conclusion encoded by the stated correctness condition.

**Key facts.** `Randomized.expTimeLe_repeatRun`, `Randomized.randProb_mono`, `Randomized.randProb_not`, `Randomized.exists_of_repeatRun_eq_some`.

**Caveat.** The supplied informal statement says a returned bit equals the membership indicator, but the formal proof and aborting-decision hypothesis imply that it is the opposite bit. The proof account follows the formal statement’s actual conclusion.
