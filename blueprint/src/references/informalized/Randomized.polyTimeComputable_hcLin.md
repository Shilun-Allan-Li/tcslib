<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.polyTimeComputable_hcLin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Parameterized Linear Construction

**Claim.** For each natural number $n$, the function $\mathrm{hcLin}(n)$ is computable in polynomial time by a deterministic finite-state Turing machine.

**Proof.** First, the head transducer applied to the decoded first component is polynomial-time computable: compose the polynomial-time unary multiplication head transducer with the polynomial-time first-component decoder. Pair the fixed word of $n$ ones with this output, then apply unary multiplication once more; composition and polynomial-time pair encoding show this intermediate function is polynomial-time computable. Append the fixed suffix $[1,1]$ to its output, and pair that result with the decoded second component. The polynomial-time append and pair-encoding closure properties give polynomial-time computability of the resulting input to the final multiplication. A final application of polynomial-time unary multiplication, composed with this whole construction, is exactly $\mathrm{hcLin}(n)$, proving the claim.

**Key facts.** `Complexity.BinArith.polyTimeComputable_uHead`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.BinArith.polyTimeComputable_app`, `Complexity.BinArith.polyTimeComputable_mulU`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_const`, `Complexity.PolyTimeComputable.append`, `Complexity.polyTimeComputable_pairSndD`.
