<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arPos_coords -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Block Coordinates Recover Positions

**Claim.** For every $N$ and integer position $p$, the quotient and remainder coordinates of $p$ reconstruct $p$ as $(N+1)q+s$.

**Proof.** Set $d=N+1$, which is positive, and write $p=dq+r$ by integer division with remainder, where $q=p/d$ and $r=p\bmod d$. The remainder is nonnegative, so its conversion to a natural number preserves its value. By the definition of the block position, $\mathrm{arPos}(N,q,r)=dq+r=p$.
