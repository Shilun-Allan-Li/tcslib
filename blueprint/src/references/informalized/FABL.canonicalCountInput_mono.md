<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.canonicalCountInput_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of canonical count inputs

**Claim.** If $k\le l$, then the canonical count input for $k$ is coordinatewise at most the canonical count input for $l$.

**Proof.** Fix a coordinate $i$. If $i<k$, then also $i<l$, so both inputs have value $1$ there. If $i\not<k$ but $i<l$, the values are $-1$ and $1$, respectively, and the inequality follows because $-1$ is at most every sign (`neg_one_le_sign`). If $i\not<l$, then also $i\not<k$, so both values are $-1$. These cases prove the coordinatewise inequality.

**Key facts.** `FABL.neg_one_le_sign`.
