<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.readFrame_reg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register update preserves the read frame

**Claim.** Under the stated distinctness and head-position assumptions, updating tape $s$ and its head after the read configuration yields a configuration in the read frame of $c$, with the specified head-position bounds.

**Proof.** Take the witness for the read frame to be the resulting state $l'$, input position $ip$, updated tape content $f$, tape-$s$ head position $p$, and tape-$r$ head position $0$. By definition, the register update changes the state, tape $s$, and its head while leaving the input position and output as specified. Since $r\ne s$, updating tape $s$ does not alter tape $r$; its head remains at the original position $0$. The assumed bounds give the required interval for $p$, and $0$ lies in that interval as well.
