<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/PowTable.lean :: Light.powTable_ends -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power Table Construction

**Claim.** Under the stated space, word-bound, and power bounds, the power-table procedure finishes within time $17L+8$, writes $1,b,b^2,\ldots,b^{L-1}$ into the length-$L$ segment starting at $\mathrm{dst}$, and preserves memory outside that segment.

**Proof.** First, the word bound accommodates $1$, since the power bound at exponent zero gives $1\le W$. Initialize the stored power to $1$ and the loop index to zero. Use the loop invariant that, after $j$ rounds, the first $j$ cells contain $1,b,\ldots,b^{j-1}$, the current power is $b^j$, and memory outside the destination segment still agrees with its initial contents. The loop rule for a counted loop (`Light.Ends.for`) packages this invariant: its start condition holds after initialization, and its bound condition follows from the assumed word bounds through exponent $L$. In round $j<L$, store the current power $b^j$ at position $\mathrm{dst}+j$, then multiply the current power by $b$ to obtain $b^{j+1}$. The exponent bound through $L$ makes this update safe; the address fits because $\mathrm{dst}+L\le S$. The new store changes only the current segment cell, so the outside-memory condition persists. When the loop ends, the invariant gives the required values in every cell. The list-entry identity for the power list (`Light.getElem_powList`) identifies these values with the specified segment, and the loop rule's time estimate, together with the initialization cost, yields the stated bound.

**Key facts.** `Light.Ends.for`, `Light.getElem_powList`.
