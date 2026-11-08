<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.sealGates_fanout -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanout bound after sealing

**Claim.** Under the stated acyclicity, index, and fanout hypotheses, sealing the indices in $L$ preserves the bound that every index has fanout at most two.

**Proof.** Proceed by induction on the list of indices to seal. The empty list changes nothing. For the step, let $u$ be the first index and set $N=n+|gs|$. The hypotheses give $u<N$ and ensure the current output $o<N$. The sealing step appends three gates: NOT on $u$, OR on $u,N$, and AND on $o,N+1$, and updates the output to $N+2$. These gates are acyclic after the old list: the old list is acyclic, and the three new gates are acyclic relative to the old list's endpoint (by the append criterion for acyclicity and the acyclicity of the sealing triple, `gatesAcyclic_append` and `sealTriple_acyclic`). The new list has length $|gs|+3$, so the induction hypotheses apply to the remaining indices, which remain below its endpoint; they are still distinct, and the new output is not among them.

It remains to check the induction's fanout conditions for this enlarged list. Fanout is additive under list append (`fanoutIn_append`), and the three new gates contribute two reads of $u$, one of $N$, one of $o$, and one of $N+1$ (`fanoutIn_sealTriple`). Each remaining sealed index previously had fanout zero; it is distinct from $u,o$, and lies below $N$, so it is none of the newly introduced indices. Its fanout therefore remains zero. The new output $N+2$ has fanout zero in the old list by acyclicity and has no reads in the triple, so its fanout is at most one. Finally, for any index, separate the cases that it is $u$, is $o$, is below $N$ and different from both, or is at least $N$ and different from both. In the first case the two new reads are offset by $u$'s old fanout zero; in the second the single new read is offset by the old output's fanout at most one; in the third the new gates add no reads; and in the last case old acyclicity gives fanout zero, while the triple contributes at most one read. Thus all indices still have fanout at most two, and induction completes the argument.

**Key facts.** `BoolCircuit.gatesAcyclic_append`, `BoolCircuit.sealTriple_acyclic`, `BoolCircuit.fanoutIn_append`, `BoolCircuit.fanoutIn_sealTriple`, `BoolCircuit.fanoutIn_eq_zero_of_le`.
