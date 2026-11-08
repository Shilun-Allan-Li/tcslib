<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clAddColumn_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Addition Column Identity

**Claim.** For Boolean bits $c,u,v$, the sum of their numeric values equals twice the outgoing carry value plus the low result bit value, where the low result bit is their exclusive-or and the outgoing carry is their majority bit.

**Proof.** There are only eight choices for $(c,u,v)$. For each, the low bit given by the exclusive-or and the carry given by the majority satisfy the identity: with zero or one true input the sum and encoded output are respectively $0$ or $1$; with two true inputs they are $2=2\cdot1+0$; with three they are $3=2\cdot1+1$. This verifies the identity in every case.
