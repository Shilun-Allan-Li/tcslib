<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.minimumPositiveAtom_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the Minimum Positive Atom

**Claim.** For a probability mass function $p$ on a finite set, the minimum mass among points of positive mass is at most $1$.

**Proof.** Choose a point $x$ in the positive support, which exists because the support is nonempty (`pmfPositiveSupport_nonempty`). By the definition of positive support, $p(x)\ne 0$. The minimum positive atom is at most the mass at any point of positive mass (`minimumPositiveAtom_le`), so it is at most $(p(x)).toReal$. Every probability mass is at most $1$ after conversion to a real number (`pmf_apply_toReal_le_one`). Combining these inequalities gives the result.

**Key facts.** `FABL.pmfPositiveSupport_nonempty`, `FABL.minimumPositiveAtom_le`, `FABL.pmf_apply_toReal_le_one`.
