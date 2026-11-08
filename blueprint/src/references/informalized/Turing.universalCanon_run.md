<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universalCanon_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonizer run in the buffered composition

**Claim.** For each $t\in\mathbb N$, there is a Boolean flag $b$ such that the buffered composition, started on the paired input $\langle\alpha,x\rangle$, reaches after $3|\alpha|+4+t$ steps the buffered second-phase configuration containing the canonizer’s configuration after $t$ steps on $\alpha$, with physical input head at position $2|\alpha|+3$.

**Proof.** First, the prefix-parsing phase reaches the buffered second-phase configuration after $3|\alpha|+4$ steps, with the canonizer initialized on $\alpha$, flag true, physical input head at $2|\alpha|+3$, and the other buffered tapes in their initial settings (\texttt{universalCanon\_start}). Split the total run into this initial segment and a further $t$ steps, using the run concatenation law (\texttt{runFrom\_add}). The buffered second-machine simulation lemma says that, starting from a second-phase configuration whose flag satisfies the virtual-boundary condition, the next $t$ steps track the second machine’s $t$-step run in the buffer. The initial flag satisfies that condition; the lemma supplies a resulting flag $b$ and the desired equality of configurations. The paired-input length identity (\texttt{universal\_pair\_length}) ensures the stated physical head position is a valid position on the paired input.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.universalCanon_start`, `Turing.FinTM.bufferedSecondCfg_run`, `Turing.universal_pair_length`.
