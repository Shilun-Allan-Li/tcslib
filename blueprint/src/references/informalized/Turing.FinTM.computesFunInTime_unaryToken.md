<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.computesFunInTime_unaryToken -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear-time unary-token encoding

**Claim.** A finite Turing machine over the Boolean alphabet outputs the pair encoding of the maximal initial run of $1$ bits, including the first following $0$ when present, and the remaining suffix, in time bounded by $3(n+1)$ on every input of length $n$.

**Proof.** Choose the unary-token machine and the constant $c=3$. For an input $x$, the machine's run lemma (`emitterToken_run`) says that, from the scanning configuration, after $2|u|+|r|+3$ steps it halts and appends the pair encoding of the token and remainder obtained by splitting the unprocessed suffix. Apply this with the entire input as that suffix and empty prefix and output. The initial configuration is exactly the corresponding scanning configuration, since both have the initial state, input-head position, and empty output; the machine has no work tapes. Thus the run halts with the required output after $2|u|+|r|+3$ steps, where $(u,r)=	ext{unaryTokenSplit}(x)$. The length identity $|u|+|r|=|x|$ (`emitterToken_length`) gives $2|u|+|r|+3\le 3(|x|+1)$. This establishes the stated uniform time bound.

**Key facts.** `Turing.FinTM.emitterToken_run`, `Turing.Cfg.ext_zero_tapes`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.emitterToken_length`, `Turing.FinTM.ComputesInTime.mono`.
