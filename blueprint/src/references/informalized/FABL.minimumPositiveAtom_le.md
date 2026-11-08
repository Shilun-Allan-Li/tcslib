<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.minimumPositiveAtom_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound by the Minimum Positive Atom

**Claim.** For a finite probability mass function $p$, if $x$ has nonzero mass, then the minimum mass among points of positive mass is at most the mass of $x$.

**Proof.** The assumption $p(x)\ne0$ places $x$ in the positive support of $p$. The minimum positive atom is the infimum of the real-valued masses over this finite nonempty support. An infimum of a finite set is at most every member of that set; applying this to $x$ gives the claimed inequality.
