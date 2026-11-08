<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.width_le_clog_tribesCriticalDimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Dimension Lower Bound

**Claim.** For every integer $w\ge 4$, the width $w$ is at most the base-$2$ ceiling logarithm of the tribes critical dimension at width $w$.

**Proof.** The lower bound on the tribes critical size gives $2^{w-2}\le \operatorname{tribesCriticalSize}(w)$ (two_pow_sub_two_le_tribesCriticalSize). Also, $2^w=4\cdot 2^{w-2}$, and $4\le w$; multiplying the size bound by $w$ therefore gives $2^w\le w\operatorname{tribesCriticalSize}(w)$. The critical dimension is the size times $w$, so commutativity of multiplication yields $2^w\le \operatorname{tribesCriticalDimension}(w)$. The base-$2$ ceiling logarithm of $2^w$ is $w$, and this ceiling logarithm is monotone in its argument. Applying monotonicity to the dimension inequality proves the result.

**Key facts.** `FABL.two_pow_sub_two_le_tribesCriticalSize`.
