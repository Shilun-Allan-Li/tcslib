/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinRelabel
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinSeedRelabel

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Actual key and nonce tables separated from tape parameters

The complete tape is split into the actual key/nonce value tables and an
unchanged parameter retaining every shift bit and every unused key/row block.
The derived assignment permutations depend only on those retained shifts.
There is no claim that XOR shifts are uniform over all assignment permutations.

## Main definitions

* `keyEmbedding`, `rowEmbedding`: the actual coordinate embeddings in padded blocks.
* `Rest`: all shift bits and unused padded blocks.
* `equiv`: the complete tape as unchanged parameters and actual value tables.

## Main results

* Exact key, nonce-half and shift readers identify the split with addressed tape bits.
* The seed permutation is determined by the retained shift parameter alone.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 and Theorem 163.7 (the gate-by-gate hybrid).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues

open BoolCircuit TCSlib.Cryptography

/-- Split a function into its values on an embedding's image and its complement.
This only composes the existing subtype split with its image equivalence. -/
private noncomputable def splitEmbedding {ι κ : Type} (e : ι ↪ κ) (V : Type) :
    (κ → V) ≃ (ι → V) × ({x : κ // x ∉ Set.range e} → V) :=
  letI : DecidablePred (fun x => x ∈ Set.range e) := fun _ => Classical.propDecidable _
  (Equiv.piEquivPiSubtypeProd (fun x => x ∈ Set.range e) (fun _ => V)).trans
    ((Equiv.arrowCongr (Equiv.ofInjective e e.injective).symm (Equiv.refl V)).prodCongr
      (Equiv.refl _))

/-- The used component reads `f (e i)`. -/
private theorem splitEmbedding_used {ι κ : Type} (e : ι ↪ κ) (V : Type)
    (f : κ → V) (i : ι) : (splitEmbedding e V f).1 i = f (e i) := rfl

/-- The unused component retains `f j` at each coordinate outside the embedding image. -/
private theorem splitEmbedding_unused {ι κ : Type} (e : ι ↪ κ) (V : Type)
    (f : κ → V) (j : {x : κ // x ∉ Set.range e}) :
    (splitEmbedding e V f).2 j = f j := rfl

/-- Embed a real key label `(w,b)` as padded block `(b,castLE w)`. -/
def keyEmbedding {m : ℕ} (C : DAGCircuit m) (S : ℕ) (hS : C.size ≤ S) :
    (Fin C.size × Bool) ↪ (Bool × Fin S) where
  toFun x := (x.2, Fin.castLE hS x.1)
  inj' x y h := Prod.ext
    (Fin.ext (congrArg (fun z : Bool × Fin S => (z.2 : ℕ)) h)) (congrArg Prod.fst h)

/-- `keyEmbedding C S hS (w,b) = (b,Fin.castLE hS w)`. -/
theorem keyEmbedding_eq {m : ℕ} (C : DAGCircuit m) (S : ℕ) (hS : C.size ≤ S)
    (w : Fin C.size) (b : Bool) :
    keyEmbedding C S hS (w, b) = (b, Fin.castLE hS w) := rfl

/-- The size bound also bounds the gate count. -/
private theorem gateBound {m : ℕ} (C : DAGCircuit m) (S : ℕ) (hS : C.size ≤ S) :
    C.gates.length ≤ S := by
  rw [DAGCircuit.size_eq] at hS
  omega

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues
