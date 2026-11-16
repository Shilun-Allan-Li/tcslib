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
  inj' _ _ h := Prod.ext
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

/-- Embed a real gate/assignment row as its gate coordinate and binary-fold code.
Only actual assignments are used, leaving padded and unused row codes separate. -/
def rowEmbedding {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2)
    (hS : C.size ≤ S) :
    (Σ i : Fin C.gates.length, (Fin (C.gates[i.val]).args.length → Bool)) ↪ (Fin S × Fin 4) where
  toFun x := (Fin.castLE (gateBound C S hS) x.1,
    CoinSeedRelabel.assignmentEmbedding (C.gates[x.1.val]).args.length (hA x.1) x.2)
  inj' := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hij : i = j := Fin.ext (congrArg (fun x : Fin S × Fin 4 => (x.1 : ℕ)) h)
    cases hij
    have hab : a = b :=
      (CoinSeedRelabel.assignmentEmbedding (C.gates[i.val]).args.length (hA i)).injective
        (congrArg Prod.snd h)
    cases hab
    rfl

/-- `rowEmbedding ... ⟨i,a⟩ = (castLE i,assignmentEmbedding ... a)` for any supplied
gate-count bound; the cast proof does not affect the coordinate. -/
theorem rowEmbedding_eq {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2)
    (hS : C.size ≤ S) (hG : C.gates.length ≤ S) (i : Fin C.gates.length)
    (a : Fin (C.gates[i.val]).args.length → Bool) :
    rowEmbedding C S hA hS ⟨i, a⟩ = (Fin.castLE hG i,
      CoinSeedRelabel.assignmentEmbedding (C.gates[i.val]).args.length (hA i) a) := rfl

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues
