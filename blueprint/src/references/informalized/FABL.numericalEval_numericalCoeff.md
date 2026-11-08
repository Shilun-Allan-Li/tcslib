<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/NumericalNormalForm.lean :: FABL.numericalEval_numericalCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the chosen coefficient function

**Claim.** For every pseudo-Boolean function, evaluating the coefficient function selected by the uniqueness theorem recovers that function.

**Proof.** The uniqueness theorem (`existsUnique_numericalEval`) supplies a coefficient function whose numerical evaluation is the given function, together with uniqueness of that coefficient function. The definition of `numericalCoeff` chooses this witness. Its evaluation equation is therefore the existence part of that unique-witness statement.

**Key facts.** `FABL.existsUnique_numericalEval`.

**Caveat.** The informal statement describes several exercises, but the supplied formal declaration proves only the evaluation identity for the coefficient function chosen from the existence-and-uniqueness theorem.
