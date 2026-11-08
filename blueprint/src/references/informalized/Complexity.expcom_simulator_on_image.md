<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/EXPCOM.lean :: Complexity.expcom_simulator_on_image -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulator Runtime on Front-Transformed Inputs

**Claim.** For every Boolean word z, the fixed simulator halts on the front transformation of z, outputs the bit indicating whether z belongs to EXPCOM, and does so within the stated time bound.

**Proof.** Split according to whether z passes the validity test. If it does, the validity characterization (expcom_ok_iff) writes z as the nested encoding of some α, x, and n true bits. The front-on-triples identity (expcom_front_triple) identifies its transformed input with the simulator encoding for α, x, and the binary representation of $2^n$. The input length bounds both α and x together and also bounds n, so monotonicity of powers and multiplication bounds the simulator's promised time at parameter $2^n$ by the claimed time bound. By the encoded-triple membership equivalence (expcom_mem_triple), acceptance by the decoded machine at exactly $2^n$ steps is equivalent to z belonging to EXPCOM. The simulator's acceptance or rejection guarantee therefore gives the required indicator bit, and its computation can be extended to the claimed time using monotonicity of computation time (ComputesInTime.mono). If z fails the validity test, it cannot belong to EXPCOM, since any EXPCOM witness would make the validity characterization apply. The simulator is then run on the fixed default input, using its rejection guarantee with a machine that cannot compute in zero steps (not_computesInTime_zero). This gives the required output in the simulator's fixed degree number of steps, which is at most the stated bound because the latter's base is at least one.

**Key facts.** `Complexity.expcom_ok_iff`, `Complexity.expcom_front_triple`, `Turing.length_pairEncode`, `Complexity.expcom_mem_triple`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.not_computesInTime_zero`.
