<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BLR.lean :: FABL.exists_closestInProperty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Closest Property Member

**Claim.** If a property of functions on a finite nonempty domain is nonempty, then it contains a function minimizing the relative Hamming distance from any fixed function.

**Proof.** Choose one function satisfying the property, and regard all property-satisfying functions as a subtype of the function space. This subtype is nonempty by the hypothesis. Since the domain and codomain are finite, the function space—and hence the subtype—is finite. A real-valued function on a nonempty finite type attains a minimum, so choose a property member attaining the minimum relative Hamming distance. Its minimality among the subtype gives the stated inequality against every other property member.
