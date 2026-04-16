import TCSlib.BooleanAnalysis.Switching.Defs
import TCSlib.BooleanAnalysis.Switching.CanonicalDTree
import TCSlib.BooleanAnalysis.Switching.Encoding
import TCSlib.BooleanAnalysis.Switching.EncodingProperties
import TCSlib.BooleanAnalysis.Switching.RoundTrip

/- import TCSlib.BooleanAnalysis.Switching.Switching

/-!
# Håstad's Switching Lemma — Razborov's Decision-Tree Path Encoding

An implementation of Håstad's Switching Lemma (1987) via Razborov's proof.

## Module structure

- `Switching.Defs`: Restrictions, literal/term effects, basic lemmas
- `Switching.CanonicalDTree`: Canonical decision tree construction and correctness
- `Switching.Encoding`: Razborov encoding/decoding definitions
- `Switching.EncodingProperties`: Properties of the encoding (stability, bounds, etc.)
- `Switching.RoundTrip`: Round-trip proof (decode ∘ encode = id)
- `Switching.MainTheorem`: Switching lemma statement and corollary

## References

* J. Håstad, *Computational Limitations of Small-Depth Circuits*, MIT Press, 1987.
* A. Razborov, simplified proof of the switching lemma.
* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014.
-/
