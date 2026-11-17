<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clFields_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for Packed Fields

**Claim.** If every word in a finite list $ws$ of Boolean words has length at most $W$, then the packed encoding of $ws$ has length at most $|ws|(2W+2)$.

**Proof.** Induct on $ws$. The empty list has packed encoding of length zero. For the step, write the list as $w::ws$. Its packed encoding consists of two copies of each bit of $w$, a two-bit separator, and the packed encoding of the tail; hence its length is $2|w|+2+|\mathrm{clFields}(ws)|$. The hypothesis bounds $|w|$ by $W$, and the induction hypothesis bounds the tail length by $|ws|(2W+2)$. Adding these bounds gives $(2W+2)+|ws|(2W+2)=(|ws|+1)(2W+2)$, as required.
