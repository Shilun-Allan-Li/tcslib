<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.hasDepthCircuit_parity_canonical -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical parity circuit bounds

**Claim.** For every pair of natural numbers \(n,q\), parity on all \(n\) coordinates has a circuit of depth exactly \(q+3\), size at most \((q+2)b^{q+1}2^b\), and width at most \(n\), where \(b=\max\{1,\lceil n^{1/(q+2)}\rceil\}\).

**Proof.** Set \(r=b\) and take the circuit built from blocks, \(C=\texttt{parityDepthCircuitFromBlocks}\,n\,r\,q\). Its depth is exactly \(q+3\) (\(\texttt{FABL.depth_parityDepthCircuitFromBlocks}\)). Since \(r\ge1\) (\(\texttt{FABL.one_le_parityBlockSide}\)), its size is at most \((q+2)r^{q+1}2^r\) (\(\texttt{FABL.size_parityDepthCircuitFromBlocks_le}\)). Every circuit on this cube has width at most the dimension \(n\) (\(\texttt{FABL.DepthCircuit.width_le_dimension}\)). To see that the block circuit computes parity on all coordinates, use \(q+2>0\) and the covering bound \(n\le r^{q+2}\) (\(\texttt{FABL.parityBlockSide_pow_covers}\)); the circuit's represented function is then the full parity function (\(\texttt{FABL.toBooleanFunction_parityDepthCircuitFromBlocks}\)). Substituting \(r=b\) gives the stated size bound.

**Key facts.** `FABL.depth_parityDepthCircuitFromBlocks`, `FABL.one_le_parityBlockSide`, `FABL.size_parityDepthCircuitFromBlocks_le`, `FABL.DepthCircuit.width_le_dimension`, `FABL.parityBlockSide_pow_covers`, `FABL.toBooleanFunction_parityDepthCircuitFromBlocks`.
