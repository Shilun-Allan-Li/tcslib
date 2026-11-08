<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridge_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure of Statement Support Under Substatements

**Claim.** If a compiled statement belongs to the finite statement support and a second statement is an immediate substatement of it, then the second statement also belongs to that support.

**Proof.** The statement support is generated from the compilation's code support by closing under the compiled transition's substatements. The transitivity property for this closure says that an immediate substatement of a supported statement is supported as well (`TM2.stmts_trans`), which gives the claim.
