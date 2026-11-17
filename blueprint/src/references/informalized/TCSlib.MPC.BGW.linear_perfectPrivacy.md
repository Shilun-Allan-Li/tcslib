<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/MPC/BGW/Privacy.lean :: TCSlib.MPC.BGW.linear_perfectPrivacy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Privacy for Linear Circuits

**Claim.** When $|B|<k$, any two input assignments admit a bijection of the families of input polynomials of degree less than $k-1$ that makes every party in $B$ see the same BGW evaluation on every linear circuit.

**Proof.** The strict size bound says that $B$ is unauthorized for the threshold-$k$ access structure. Perfect privacy of the vector Shamir scheme (`vecScheme_perfectPrivacy`) therefore supplies a bijection of the polynomial families such that, for each polynomial family and each party in $B$, the dealt input shares for the two assignments agree coordinate by coordinate. Apply the fact that linear-circuit evaluation at a fixed party depends only on the input shares seen by that party (`bgwEval_congr_of_isLinear`). The coordinatewise agreement then gives the required equality for every linear circuit.

**Key facts.** `TCSlib.Shamir.vecScheme_perfectPrivacy`, `TCSlib.MPC.BGW.bgwEval_congr_of_isLinear`.
