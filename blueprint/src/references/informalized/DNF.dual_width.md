<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: DNF.dual_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of the Dual Formula

**Claim.** For every DNF formula $\varphi$, its De Morgan dual CNF has the same width as $\varphi$.

**Proof.** Expanding the definitions, both widths take the maximum term or clause length, with the empty maximum set to zero. The dual negates each literal in each term but leaves the lists of literals and the outer list structure unchanged. Thus corresponding lists have the same lengths, and the two widths are equal.
