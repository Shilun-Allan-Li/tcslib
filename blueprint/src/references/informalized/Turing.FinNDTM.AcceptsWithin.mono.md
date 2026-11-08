<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NTIME.lean :: Turing.FinNDTM.AcceptsWithin.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Nondeterministic Acceptance

**Claim.** If some choice word of length exactly $t$ leads $N$ on input $x$ to a halted configuration with output $[1]$, then for every $t'\ge t$ some choice word of length exactly $t'$ does so as well.

**Proof.** Choose a witnessing word $w$ of length $t$. Extend it by $t'-t$ copies of the choice $0$. The resulting word has length $t+(t'-t)=t'$. Running on the concatenation first runs the original word and then the padding. Because the configuration reached after $w$ is halted, further choices leave it unchanged (`Turing.NDTM.runWith_of_halt`); hence the extended word reaches the same halted configuration and retains output $[1]$.

**Key facts.** `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt`.
