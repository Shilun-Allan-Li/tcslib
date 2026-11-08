<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.rp_error_reduction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Amplification of Randomized Verifiers

**Claim.** If a language has a verifier with perfect rejection outside the language and acceptance probability at least $\min(2/3,(|x|+1)^{-c})$ on members, then for every $d$ it has such a verifier with acceptance probability at least $1-2^{-((|x|+1)^d+1)}$, using polynomially many random bits.

**Proof.** Take the given verifier and run it on $K=4(|x|+1)^{c+d}$ consecutive blocks, each of length $q=a(|x|+1)^k$, where $a(|x|+1)^k$ is the original random-bit bound. Accept if at least one block accepts. Closure of the verifier model under this repeated “any” test supplies the required efficiency, and the total random-bit count is $Kq=(4a)(|x|+1)^{c+d+k}$. Fix an input $x$ in the language, and let $s$ be the acceptance probability on one block. The elementary probability bounds give $0\le s\le1$. With $y=(|x|+1)^c\ge1$, the assumed lower bound implies $s\ge (2/3)y^{-1}$, hence $2(|x|+1)^c s\ge1$. Also, $K\ge 2(|x|+1)^c((|x|+1)^d+1)$. The probability that none of the independent blocks accepts is $(1-s)^K$: the block-count formula gives this probability by taking the zero-acceptance count, and identifying acceptance of the repeated verifier with the complement of that event yields its success probability as $1-(1-s)^K$. The amplification inequality now bounds the failure probability by $2^{-((|x|+1)^d+1)}$, proving the desired success bound. Finally, for $x$ outside the language, every block rejects by the original perfect-rejection property, so the repeated verifier rejects on every random string. For this last point, each length-$q$ block extracted from a length-$Kq$ random string can be represented as a length-$q$ bit vector (Randomized.exists_ofFn_eq), to which the original rejection guarantee applies.

**Key facts.** `Randomized.randProb_nonneg`, `Randomized.randProb_le_one`, `Randomized.randProb_blockCount`, `Randomized.randProb_congr`, `Randomized.randProb_not`, `Randomized.one_sub_pow_le_half_pow`, `Randomized.exists_ofFn_eq`.
