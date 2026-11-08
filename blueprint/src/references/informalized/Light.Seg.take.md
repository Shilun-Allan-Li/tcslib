<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.Seg.take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Taking an Initial Segment

**Claim.** If $l$ records the values of $\mu$ starting at $a$, then the initial list formed by taking the first $k$ entries of $l$ does too.

**Proof.** Fix an index $i$ in the list $l$ take $k$. Such an index is also less than $|l|$. The original segment property therefore gives $\mu(a+i)=l_i$. For an in-range index, taking an initial list preserves that entry, so $l_i=(l\mathbin{\mathrm{take}}k)_i$. Combining these equalities proves the required segment property.
