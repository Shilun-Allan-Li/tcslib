import TCSlib.BooleanAnalysis.Hypercontractivity.Applications
import TCSlib.BooleanAnalysis.Hypercontractivity.Bonami
import TCSlib.BooleanAnalysis.Hypercontractivity.Decomposition
import TCSlib.BooleanAnalysis.Hypercontractivity.EvenMoments
import TCSlib.BooleanAnalysis.Hypercontractivity.General
import TCSlib.BooleanAnalysis.Hypercontractivity.OneBit
import TCSlib.BooleanAnalysis.Hypercontractivity.MomentBounds
import TCSlib.BooleanAnalysis.Hypercontractivity.ReverseBonamiBeckner

/-!
# Hypercontractivity

This umbrella module re-exports the Boolean-cube hypercontractivity development: coordinate
decomposition, one-bit and general hypercontractive inequalities, moment bounds, small-set
expansion applications, Bonami's lemma, and the reverse Bonami--Beckner outline.

## Main contents

* `Decomposition`, `OneBit`, `EvenMoments`, and `General`: the forward hypercontractivity theory.
* `Bonami` and `MomentBounds`: fourth-moment and anticoncentration tools.
* `Applications` and `ReverseBonamiBeckner`: small-set expansion and reverse-hypercontractivity
  results.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, Chapters 9--10.
-/
