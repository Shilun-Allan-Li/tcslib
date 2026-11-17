<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean :: Complexity.LogProg.valPrefix_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary-prefix validation run

**Claim.** Under the stated transition identities and no-call assumptions, the machine reaches state $vX$ at position $3+tRun(x)$ when the initial run of ones has even length and is followed by $01$. If that condition fails, it halts with a rejecting output; the run avoids call states before its endpoint.

**Proof.** Let $t=tRun(x)$. Alternate $vU0$ and $vU1$ while scanning the initial run of ones. Every bit before position $t$ is true (`getElem?_lt_tRun`), so each transition advances one place; `scanR` records the resulting configurations and their no-call property. Consequently the machine reaches the state selected by the parity of $t$ at position $1+t$.

Inspect the bit at $t$. If it is absent, the machine rejects at the boundary. It cannot be true, by the defining property of $t$ (`getElem?_tRun`). Thus it is false; if $t$ is odd, the machine rejects in state $vU1$. If $t$ is even, it enters the separator-check state $vS$. The next bit must be true: if absent or false, the machine rejects. If true, the next transition enters $vX$ at position $3+t$. These transitions advance the input head one position at a time (`reaches_right`), and `inSym_succ` identifies the symbols read at the one-based positions. The bounds from $t\le |x|$ (`tRun_le`) make the endpoint position valid.

The reachability segments are joined using `Reaches.step`, `Reaches.trans`, and the zero-length continuation `Reaches.refl`; if an inspected bit forces rejection, `rejects_one` supplies that terminal rejection and `Reaches.rejects` prefixes the already completed scan. The parity and bit checks are exactly the stated condition, so the two implications follow, with the scan witnesses preserving the register positions and avoiding call states.

**Key facts.** `Complexity.LogProg.tRun_le`, `Complexity.LogProg.scanR`, `Complexity.LogProg.getElem?_lt_tRun`, `Complexity.LogProg.getElem?_tRun`, `Complexity.LogProg.inSym_succ`, `Complexity.LogProg.reaches_right`, `Complexity.LogProg.rejects_one`, `Complexity.LogProg.Reaches.step`, `Complexity.LogProg.Reaches.trans`, `Complexity.LogProg.Reaches.refl`, `Complexity.LogProg.Reaches.rejects`.
