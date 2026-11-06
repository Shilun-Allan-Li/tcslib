import TCSlib.Cryptography.Candidates.RSA
/-! Seal controls (fill rsa): three readings of foreign definitions, each closing unsealed and
failing sealed. -/
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Candidates NumberTheory

namespace RsaSealUnsealed
example (k N : ℕ) : natToList k N = List.ofFn (natToBits k N) := rfl
example (z : List Bool) : NUPPT.inParam z = pairFstD (pairFstD (pairFstD z)) := rfl
example (z : List Bool) :
    leStr z = [decide (listToNat (pairFstD z) ≤ listToNat (pairSndD z))] := rfl
end RsaSealUnsealed

namespace RsaSealSealed
attribute [local irreducible] natToList NUPPT.inParam leStr
example (k N : ℕ) : natToList k N = List.ofFn (natToBits k N) := rfl
example (z : List Bool) : NUPPT.inParam z = pairFstD (pairFstD (pairFstD z)) := rfl
example (z : List Bool) :
    leStr z = [decide (listToNat (pairFstD z) ≤ listToNat (pairSndD z))] := rfl
end RsaSealSealed
