<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.hasDepthCircuit_parity_depth_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth-two parity circuit bound

**Claim.** For every $n$, parity on all $n$ coordinates is computed by a depth-two circuit of size at most $2^{\operatorname{parityBlockSide}(n,1)}$ and width at most $n$.

**Proof.** Take the DNF formula for parity and convert it to a depth-two circuit. The resulting circuit has depth exactly two (`FABL.DepthCircuit.depth_ofDNF`), has the same size as the formula (`FABL.DepthCircuit.size_ofDNF`), and computes the same function (`FABL.DepthCircuit.toBooleanFunction`). Its width is at most the number of variables by the general width bound (`FABL.DepthCircuit.width_le_dimension`). The DNF size is at most $2^n$ by the minterm DNF bound (`FABL.size_mintermDNF_le`). Since the block side with $h=1$ satisfies $n\leq \operatorname{parityBlockSide}(n,1)$ (`FABL.parityBlockSide_pow_covers`), monotonicity of powers of two gives the required size bound. The parity DNF computes parity by `FABL.parityDNF_toBooleanFunction`.

**Key facts.** `FABL.DepthCircuit.depth_ofDNF`, `FABL.DepthCircuit.size_ofDNF`, `FABL.DepthCircuit.width_le_dimension`, `FABL.size_mintermDNF_le`, `FABL.parityBlockSide_pow_covers`, `FABL.DepthCircuit.toBooleanFunction_ofDNF`, `FABL.parityDNF_toBooleanFunction`.

**Caveat.** The supplied informal statement mentions an exact size bound and term width, but the formal theorem and its proof establish only the stated depth-two circuit upper bound and width-at-most-dimension claim.
