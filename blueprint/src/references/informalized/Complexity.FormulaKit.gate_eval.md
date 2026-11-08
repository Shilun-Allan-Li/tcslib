<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/FormulaKit/Gate.lean :: Complexity.FormulaKit.gate_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Gate

**Claim.** For every natural number $\ell$, Boolean function $p$ on vectors indexed by $\{0,\ldots,\ell-1\}$, wire map $\mathrm{wire}:\mathbb{N}\to\mathbb{N}$, and Boolean assignment $a$ on the natural numbers, the gate evaluates to $p$ applied to the vector whose value at index $i$ is $a(\mathrm{wire}(i))$.

**Proof.** The gate is the template for $p$ with each variable relabeled by its corresponding wire. The evaluation-under-relabeling identity says that evaluating this relabeled formula at $a$ is the same as evaluating the template at the assignment that sends index $i$ to $a(\mathrm{wire}(i))$. The template evaluation theorem (Complexity.FormulaKit.template_eval) identifies that evaluation with $p$ applied to precisely this vector, proving the claim.

**Key facts.** `Complexity.FormulaKit.template_eval`.
