<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/BalancedSimulation.lean :: CommunicationComplexity.Deterministic.Protocol.simulation_step_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Balanced arithmetic bound

**Claim.** Under the stated bounds on the two complexities and the balance conditions on $m$ and $n-m$, the claimed inequality holds for the maximum of the complexities.

**Proof.** First bound the term with the larger complexity exponent by the corresponding squared quantity: if $c_{\mathrm{in}}\le c_{\mathrm{out}}$, use the hypothesis for $c_{\mathrm{out}}$ and enlarge $(n-m)^2$ to the maximum of the two squares; if $c_{\mathrm{out}}\le c_{\mathrm{in}}$, use the other hypothesis and enlarge $m^2$ in the same way. Thus $3^{\max(c_{\mathrm{in}},c_{\mathrm{out}})}\le 2^{\max(c_{\mathrm{in}},c_{\mathrm{out}})}\max(m^2,(n-m)^2)$. The balance conditions imply $9\max(m^2,(n-m)^2)\le 4n^2$ (`max_sq_le_of_balanced`). Multiply the first bound by $9$, apply this latter inequality, and rearrange using $3^2=9$ and $2^2=4$. The result is $3^{2+\max(c_{\mathrm{in}},c_{\mathrm{out}})}\le 2^{2+\max(c_{\mathrm{in}},c_{\mathrm{out}})}n^2$.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.max_sq_le_of_balanced`.
