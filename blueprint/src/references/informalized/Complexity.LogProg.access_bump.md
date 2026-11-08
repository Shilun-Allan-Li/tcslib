<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_bump -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Access Counter Increment Path

**Claim.** When $k+1$ and $p+1$ are at most $|y|+1$, a path takes the first bump state with tapes encoding $0,0,k,p$ and all heads at zero to the initial scan state with tapes encoding $0,0,k+1,p+1$ and all heads at zero.

**Proof.** First apply the counter-increment run result (`inc_run`) to tape $2$, which changes its binary word from that of $k$ to that of $k+1$ while returning its head to zero. During this run, the only head that moves is the one on tape $2$, and the increment bound keeps it between $-1$ and the bit-length of $k+1$. Since $k+1\le |y|+1$, monotonicity of binary bit-length (`length_bits_mono`) puts this within the required global upper bound. The other heads retain their safe positions by the frame property (`access_frame`). The run therefore gives an access path to the state “increment tape 3 for scan,” with tape $2$ encoding $k+1$. Next, apply the access-pointer increment result (`access_inc_pointer`) to tape $3$, using $p+1\le |y|+1$. This increments $p$ to $p+1$, restores the heads to zero, and enters the initial scan-reading state. The two paths concatenate, giving the claimed endpoint.

**Key facts.** `Complexity.LogProg.inc_run`, `Complexity.LogProg.length_bits_mono`, `Complexity.LogProg.access_frame`, `Complexity.LogProg.accessPath_of_run`, `Complexity.LogProg.access_inc_pointer`.
