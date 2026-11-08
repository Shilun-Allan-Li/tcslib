<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/WindowRun.lean :: Turing.wl_patch_record -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Patch Records Its Field List

**Claim.** If tape $r$ records the fields $f_s$ at every offset from $-1$ through the joined-word length, then patching the configuration with equal-length fields $g_s$ makes tape zero record $g_s$ over those offsets.

**Proof.** Fix an offset $p$ in the stated range. If $0\le p<L$, where $L$ is the joined-word length of the fields, the patch overwrites tape zero at the corresponding position with the value prescribed by $g_s$. Subtracting the head position from that tape position leaves offset $p$, so this is exactly the required recorded value. Otherwise, the bounds $-1\le p\le L$ force $p=-1$ or $p=L$. At either endpoint the patch interval does not overwrite the position. The original recording hypothesis therefore supplies the value there from the $f_s$ record. Since the joined lengths agree, the values prescribed by the two field lists at these boundary offsets both represent blank: at offset $-1$ this follows from the negative-offset definition of the tape encoding, and at offset $L$ from being just beyond the encoded word. Thus the retained value also equals the value prescribed by $g_s$, as required.
