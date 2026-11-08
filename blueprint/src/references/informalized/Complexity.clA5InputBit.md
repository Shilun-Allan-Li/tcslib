<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5InputBit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boundary-Aware Input Bit Formula

**Claim.** For every Boolean word $y$ and position $p$, the input read is absent unless $1\le p\le |y|$; within that range it is the bit at zero-based position $p-1$, with false as the default value.

**Proof.** By definition, the read is absent when $p=0$. For $p>0$, split according to whether $p\le |y|$. In the in-range case, $p-1<|y|$, so the optional list lookup is the actual bit at position $p-1$, packaged as an option; writing it as an option with a false default gives the stated formula. In the out-of-range case, $|y|\le p-1$, so the optional lookup is absent. These cases give the claimed boundary-aware expression.
