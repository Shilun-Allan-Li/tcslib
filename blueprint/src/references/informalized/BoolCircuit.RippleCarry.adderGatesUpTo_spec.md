<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.RippleCarry.adderGatesUpTo_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ripple-Carry Circuit Specification

**Claim.** For an input assignment $x$, if $3k\le n$ and $i\le k$, running the initial constant gates and $i$ bit blocks produces a list of length $n+2+15i$. Its carry and accumulator entries give, respectively, the carry after $i$ positions and whether all sum bits in those positions agree with the third input stream.

**Proof.** Proceed by induction on $i$. At $i=0$, the two initial gates produce the false carry and true accumulator, with the input values unchanged. These are exactly the initial values specified by the definitions of the carry and agreement sequences; the list length and the two indexed values follow directly.

For the induction step, assume the specification after $i$ blocks and use the hypothesis $i+1\le k$ to obtain the bounds needed for the next block. Running the previous gates followed by this block is the same as first evaluating the previous gates and then appending the block's gates (`BoolCircuit.runWith_append`). The previous output list has length $L=n+2+15i$. The block specification (`BoolCircuit.RippleCarry.runWith_bitBlock`) says that the new list has length $L+15$, and that its entries at offsets $L+8$ and $L+14$ are the new carry and accumulator expressions. Its other required indices are valid: the carry and accumulator indices lie below $L$ (`BoolCircuit.cinIdx_lt`, `BoolCircuit.accIdx_lt`).

The earlier circuit run does not change any input position below $n$: a run of gates preserves entries whose indices are below the initial list length (`BoolCircuit.runWith_getD_of_lt`). Since $3k\le n$ and $i+1\le k$, the positions $i$, $k+i$, and $2k+i$ are all below $n$. Thus the three input values read by the block equal the corresponding bits of $x$. Substituting these values and the induction hypotheses for the old carry and accumulator into the block's formulas gives the carry recurrence after $i+1$ positions and the agreement recurrence after $i+1$ positions. Together with the length calculation, this proves the induction step.

**Key facts.** `BoolCircuit.runWith_append`, `BoolCircuit.RippleCarry.runWith_bitBlock`, `BoolCircuit.cinIdx_lt`, `BoolCircuit.accIdx_lt`, `BoolCircuit.runWith_getD_of_lt`.
