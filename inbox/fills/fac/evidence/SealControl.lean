import TCSlib.Cryptography.Candidates.Factoring
/-! Seal controls (fill fac): three readings of foreign definitions, each closing unsealed and
failing sealed. -/
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Candidates NumberTheory

namespace FacSealUnsealed
example (k N : ℕ) : natToList k N = List.ofFn (natToBits k N) := rfl
example (z : List Bool) : NUPPT.inParam z = pairFstD (pairFstD (pairFstD z)) := rfl
example (ℓ : ℕ) (w : List Bool) : padFin ℓ w = fun i : Fin ℓ => w.getD i false := rfl
end FacSealUnsealed

namespace FacSealSealed
attribute [local irreducible] natToList NUPPT.inParam padFin
example (k N : ℕ) : natToList k N = List.ofFn (natToBits k N) := rfl
example (z : List Bool) : NUPPT.inParam z = pairFstD (pairFstD (pairFstD z)) := rfl
example (ℓ : ℕ) (w : List Bool) : padFin ℓ w = fun i : Fin ℓ => w.getD i false := rfl
end FacSealSealed
