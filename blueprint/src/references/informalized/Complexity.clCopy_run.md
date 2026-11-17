<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCopy_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Record-Copy Run

**Claim.** For every input word, valid input-head position, source word, and record, running the copier for $3|w|+3$ steps from state $0$ with source head zero yields state $4$, source head zero, the original source word, and the record followed by the self-delimiting encoding of $w$ with empty payload.

**Proof.** First apply the forward-copying result (`clCopy_forward`) with empty prefix: after $2|w|$ steps, each source bit has been copied twice, and the source head is at the end of $w$. The separator transition (`clCopy_separator`) then appends the two-bit marker $01$, enters the rewinding control, and places the source head one cell before the end. Apply the rewinding result (`clCopy_rewind`) with $j=|w|$; in $|w|+1$ steps it returns the source head to zero and enters state $4$, preserving the words. These phases total $2|w|+2+(|w|+1)=3|w|+3$ steps. By the definition of the encoding, the record appended in these phases is precisely the self-delimiting encoding of $w$ with empty payload.

**Key facts.** `Complexity.clCopy_forward`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.clCopy_separator`, `Complexity.clCopy_rewind`.
