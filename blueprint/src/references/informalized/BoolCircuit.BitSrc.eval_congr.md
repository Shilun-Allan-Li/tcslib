<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.BitSrc.eval_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Valid Bit Source

**Claim.** If two lists of previously computed Boolean blocks agree at every index below $i$, then any bit source valid for input length $n$, block width $w$, and instruction index $i$ evaluates identically using either list.

**Proof.** Split by the form of the bit source. An input source reads only from $x$, and a constant source returns its fixed Boolean, so neither depends on the block list. For a block source $(i',j)$, validity gives $i'<i$ (as well as the block-width bound). The assumed agreement at indices below $i$ therefore identifies the two blocks selected by index $i'$, and consequently their $j$th bits, including the default-false case, agree.
