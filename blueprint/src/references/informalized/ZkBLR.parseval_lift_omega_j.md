<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.parseval_lift_omega_j -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parseval for a twisted lift

**Claim.** For every residue class $j$ and function $f$, the sum of the squared moduli of the Fourier coefficients of the $j$-twisted lift is $1$.

**Proof.** Apply Parseval's identity to the function $x\mapsto\omega_k^{j f(x)}$ (\texttt{ZkFourier.parseval\_identity}). Each value has modulus $1$ because it is a root of unity (\texttt{ZkFourier.norm\_toOmega}), so the squared $L^2$ norm is the normalized sum of $1$ over the domain. The domain has $k^n$ elements (\texttt{ZkFourier.card\_ZkVec}), exactly the denominator in that average, so the squared norm and hence the Fourier sum equal $1$.

**Key facts.** `ZkFourier.parseval_identity`, `ZkFourier.norm_toOmega`, `ZkFourier.card_ZkVec`.
