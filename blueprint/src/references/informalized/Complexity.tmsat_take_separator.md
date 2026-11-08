<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_take_separator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Step Separator Reading

**Claim.** Under the stated bit and length hypotheses, the extractor moves from state $0$ at input position $i$ to state $3$ at position $i+2$ in two steps, with unary work tape $1^m$, work head at $m-1$, and empty output.

**Proof.** The configuration’s input-symbol rule identifies the symbol under its head with the bit at the corresponding input index (\texttt{tmsat\_take\_read}). Since the bit at position $i$ is $0$, the transition from state $0$ moves right, leaves the work tape, work head, and output unchanged, and enters state $1$. Thus after the first step the input head is at $i+1$. The run equations for zero and successor steps (\texttt{runFrom\_zero}, \texttt{runFrom\_succ\_eq\_step}) reduce the two-step claim to the transition from this configuration. At position $i+1$ the scanned bit is $1$, so state $1$ moves right, moves the work head one cell left, leaves the tape and output unchanged, and enters state $3$. The input-head movement rule gives the claimed position after each right move (\texttt{moveInputPos\_pos\_of\_ne\_right}); the length hypothesis ensures neither move is blocked at the right boundary. These componentwise updates give the stated final configuration.

**Key facts.** `Complexity.tmsat_take_read`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_pos_of_ne_right`.
