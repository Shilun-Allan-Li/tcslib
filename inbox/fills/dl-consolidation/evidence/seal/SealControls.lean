/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Foundations.BitLists
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity

/-! Paired controls of the dl-consolidation seal: each example reads one TCSlib definition
through its body (`rfl`), so it must pass unsealed and fail under the whole-file seal. They cover
the definitions that the promoted lemmas and published readers are about. -/

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Composability

example (n : ℕ) : (PolyExpr.const 3).eval n = 3 := rfl
example (ℓ : ℕ) (w : List Bool) (i : Fin ℓ) : padFin ℓ w i = w.getD i false := rfl
example (d : ℕ) (j : Fin d) : zeroBits d j = false := rfl
example (q ℓ : ℕ) (x : Fin (q * ℓ) → Bool) (i : Fin q) (j : Fin ℓ) :
    FunFamily.blocks q ℓ x i j = x (finProdFinEquiv (i, j)) := rfl
example (k : ℕ) (a : List Bool) : EnsembleLemmas.padL k a = List.ofFn (padFin k a) := rfl
example (v y : Fin 2 → Bool) : xorPerm v y = fun i => xor (y i) (v i) := rfl
example (w : List Bool) : InteractiveHandler.rU w = pairFstD (pairFstD w) := rfl
example (S : FixedLengthPKScheme) (n : ℕ) :
    S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := rfl
example (S : FixedLengthScheme) (n : ℕ) :
    S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := rfl
example {m : ℕ} (y : Fin (m + m) → Bool) :
    (FixedLengthScheme.splitHalf y).1 = fun i => y (Fin.castAdd m i) := rfl
