<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.codeReadWork_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-action decoding after encoding

**Claim.** For every optional work-tape write $w$, head movement $m$, and bit string $x$, the work-action reader succeeds on the encoding of $w$ followed by the encoding of $m$ and then $x$, returning $(w,m)$ and suffix $x$.

**Proof.** The work-action reader first decodes the optional write and then decodes the head movement from the remaining list. The optional-write decoding-after-encoding fact (`Turing.codeReadWrite_append`) says that the first stage consumes precisely the encoding of $w$ and leaves the movement encoding followed by $x$. The sign decoding-after-encoding fact (`Turing.codeReadSign_append`) then consumes precisely the movement encoding and leaves $x$. The reader therefore returns the stated pair and suffix.

**Key facts.** `Turing.codeReadWrite_append`, `Turing.codeReadSign_append`.
