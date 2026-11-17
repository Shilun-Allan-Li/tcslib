<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.Start.sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reestablishing a start configuration

**Claim.** The given code, position bound, width bound, bounded state, and memory relation establish the start conditions for $t$ at the same depth and stack position.

**Proof.** A start configuration consists of a framed memory relation, lower and upper bounds on the stack position, code placement and length bounds, a width bound, a bounded state, and the room inequality. Keep the original framed lower and upper stack bounds and room inequality from the start configuration for $s$. The hypotheses provide the required code placement, position bound, width bound, and boundedness for $t$ and $\sigma'$, while the assumed relation supplies the new framed memory relation. These components together give the start conditions for $t$.
