<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.isMonotoneInCoordinate_polarizeCoordinates_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polarization makes listed coordinates monotone

**Claim.** After successively polarizing a sign-valued function along a list of coordinates, the result is monotone in every coordinate appearing in the list.

**Proof.** Induct on the list, allowing the function being polarized to vary. The empty list has no member, so there is nothing to prove. For a list beginning with $i$, polarization along the list is polarization of the function along $i$ followed by polarization along the remaining list (\texttt{polarizeCoordinates\_cons}). If the specified coordinate is $i$, the first polarization already makes the function monotone in $i$ (\texttt{isMonotoneInCoordinate\_coordinatePolarization\_self}); subsequent polarizations preserve that monotonicity (\texttt{isMonotoneInCoordinate\_polarizeCoordinates}). If instead it occurs in the remaining list, apply the induction hypothesis to the already polarized function and that shorter list.

**Key facts.** `FABL.polarizeCoordinates_cons`, `FABL.isMonotoneInCoordinate_coordinatePolarization_self`, `FABL.isMonotoneInCoordinate_polarizeCoordinates`.
