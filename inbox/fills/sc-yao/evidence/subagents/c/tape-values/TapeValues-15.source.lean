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

/-- Decode a two-width row block into its two width-sized nonce functions. -/
private def halfEquiv (n : ℕ) :
    (Fin (2 * n) → Bool) ≃ (Fin n → Bool) × (Fin n → Bool) :=
  (Equiv.arrowCongr (finCongr (two_mul n)) (Equiv.refl Bool)).trans
    (Fin.appendEquiv n n).symm

/-- The first nonce half reads the first appended block. -/
private theorem halfEquiv_first (n : ℕ) (q : Fin (2 * n) → Bool) (t : Fin n) :
    (halfEquiv n q).1 t = q ((finCongr (two_mul n)).symm (Fin.castAdd n t)) := rfl

/-- The second nonce half reads the second appended block. -/
private theorem halfEquiv_second (n : ℕ) (q : Fin (2 * n) → Bool) (t : Fin n) :
    (halfEquiv n q).2 t = q ((finCongr (two_mul n)).symm (Fin.natAdd n t)) := rfl

/-- Separate real key blocks from all unused padded key coordinates. -/
private noncomputable def keyEquiv {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hS : C.size ≤ S) :
    (Bool → Fin S → Fin n → Bool) ≃
      (Fin C.size → Bool → Fin n → Bool) ×
        ({x : Bool × Fin S // x ∉ Set.range (keyEmbedding C S hS)} → Fin n → Bool) :=
  (Equiv.curry Bool (Fin S) (Fin n → Bool)).symm.trans
    ((splitEmbedding (keyEmbedding C S hS) (Fin n → Bool)).trans
      ((Equiv.curry (Fin C.size) Bool (Fin n → Bool)).prodCongr (Equiv.refl _)))

/-- The used key table reads its original padded key block. -/
private theorem keyEquiv_used {m : ℕ} (C : DAGCircuit m) (S n : ℕ) (hS : C.size ≤ S)
    (q : Bool → Fin S → Fin n → Bool) (w : Fin C.size) (b : Bool) :
    (keyEquiv C S n hS q).1 w b = q b (Fin.castLE hS w) := rfl

/-- The unused key table retains each complementary padded key block. -/
private theorem keyEquiv_unused {m : ℕ} (C : DAGCircuit m) (S n : ℕ) (hS : C.size ≤ S)
    (q : Bool → Fin S → Fin n → Bool)
    (x : {x : Bool × Fin S // x ∉ Set.range (keyEmbedding C S hS)}) :
    (keyEquiv C S n hS q).2 x = q x.1.1 x.1.2 := rfl

/-- Separate actual assignment rows, decoded into nonce pairs, from every unused row block. -/
private noncomputable def rowEquiv {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S) :
    (Fin S → Fin 4 → Fin (2 * n) → Bool) ≃
      ((i : Fin C.gates.length) → (Fin (C.gates[i.val]).args.length → Bool) →
        (Fin n → Bool) × (Fin n → Bool)) ×
      ({x : Fin S × Fin 4 // x ∉ Set.range (rowEmbedding C S hA hS)} → Fin (2 * n) → Bool) :=
  (Equiv.curry (Fin S) (Fin 4) (Fin (2 * n) → Bool)).symm.trans
    ((splitEmbedding (rowEmbedding C S hA hS) (Fin (2 * n) → Bool)).trans
      (((Equiv.piCurry (fun (i : Fin C.gates.length)
          (_ : Fin (C.gates[i.val]).args.length → Bool) => Fin (2 * n) → Bool)).trans
        (Equiv.piCongrRight fun i => Equiv.piCongrRight fun
          _ : Fin (C.gates[i.val]).args.length → Bool => halfEquiv n)).prodCongr
        (Equiv.refl _)))

/-- The actual nonce pair is the two halves of its padded gate/assignment block. -/
private theorem rowEquiv_used {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S)
    (q : Fin S → Fin 4 → Fin (2 * n) → Bool) (i : Fin C.gates.length)
    (a : Fin (C.gates[i.val]).args.length → Bool) :
    (rowEquiv C S n hA hS q).1 i a =
      halfEquiv n (q (Fin.castLE (gateBound C S hS) i)
        (CoinSeedRelabel.assignmentEmbedding (C.gates[i.val]).args.length (hA i) a)) := rfl

/-- The unused row table retains the complete complementary padded row block. -/
private theorem rowEquiv_unused {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S)
    (q : Fin S → Fin 4 → Fin (2 * n) → Bool)
    (x : {x : Fin S × Fin 4 // x ∉ Set.range (rowEmbedding C S hA hS)}) :
    (rowEquiv C S n hA hS q).2 x = q x.1.1 x.1.2 := rfl

/-- The retained parameter is every shift bit, every unused key block and every
unused row block, in that order. Actual key/nonce values are kept separately. -/
abbrev Rest {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S) :=
  (Fin S → Fin 2 → Bool) ×
    ({x : Bool × Fin S // x ∉ Set.range (keyEmbedding C S hS)} → Fin n → Bool) ×
    ({x : Fin S × Fin 4 // x ∉ Set.range (rowEmbedding C S hA hS)} → Fin (2 * n) → Bool)

/-- `Rest` is the product of the full shift table and the complementary padded
key and row block functions. -/
theorem Rest_eq {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S) :
    Rest C S n hA hS = ((Fin S → Fin 2 → Bool) ×
      ({x : Bool × Fin S // x ∉ Set.range (keyEmbedding C S hS)} → Fin n → Bool) ×
      ({x : Fin S × Fin 4 // x ∉ Set.range (rowEmbedding C S hA hS)} →
        Fin (2 * n) → Bool)) := rfl

/-- The complete tape is in bijection with the retained parameter and the actual
key/nonce tables. All unused padded coordinates remain in `Rest`.
This is a composition of the existing block, image-split and product equivalences.
[PS10, Theorem 163.7] -/
noncomputable def equiv {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S) :
    (Fin (10 * S * n + 2 * S) → Bool) ≃ Rest C S n hA hS ×
      ((Fin C.size → Bool → Fin n → Bool) ×
        ((i : Fin C.gates.length) → (Fin (C.gates[i.val]).args.length → Bool) →
          (Fin n → Bool) × (Fin n → Bool))) :=
  let V := Fin n → Bool
  let KU := Fin C.size → Bool → V
  let KR := {x : Bool × Fin S // x ∉ Set.range (keyEmbedding C S hS)} → V
  let RU := (i : Fin C.gates.length) → (Fin (C.gates[i.val]).args.length → Bool) → V × V
  let RR := {x : Fin S × Fin 4 // x ∉ Set.range (rowEmbedding C S hA hS)} → Fin (2 * n) → Bool
  let Shift := Fin S → Fin 2 → Bool
  let reorder : (KU × KR) × (RU × RR) × Shift ≃ (Shift × KR × RR) × KU × RU :=
    (Equiv.prodAssoc (KU × KR) (RU × RR) Shift).symm.trans
      (((Equiv.prodProdProdComm KU KR RU RR).prodCongr (Equiv.refl Shift)).trans
        ((Equiv.prodAssoc (KU × RU) (KR × RR) Shift).trans
          ((Equiv.prodComm (KU × RU) ((KR × RR) × Shift)).trans
            ((Equiv.prodComm (KR × RR) Shift).prodCongr (Equiv.refl (KU × RU))))))
  (CoinRelabel.blocksEquiv S n).trans
    (((keyEquiv C S n hS).prodCongr ((rowEquiv C S n hA hS).prodCongr
      (Equiv.refl Shift))).trans reorder)

/-- The split retains the shift and complementary block functions, and reads the
actual key blocks and both nonce halves at their embedded padded coordinates. -/
theorem equiv_eq {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S)
    (hG : C.gates.length ≤ S) (r : Fin (10 * S * n + 2 * S) → Bool) :
    equiv C S n hA hS r =
      let q := CoinRelabel.blocksEquiv S n r
      ((q.2.2, (fun x => q.1 x.1.1 x.1.2), (fun x => q.2.1 x.1.1 x.1.2)),
        (fun w b => q.1 b (Fin.castLE hS w)),
        (fun i a =>
          ((fun t => q.2.1 (Fin.castLE hG i)
            (CoinSeedRelabel.assignmentEmbedding (C.gates[i.val]).args.length (hA i) a)
            ((finCongr (two_mul n)).symm (Fin.castAdd n t))),
          (fun t => q.2.1 (Fin.castLE hG i)
            (CoinSeedRelabel.assignmentEmbedding (C.gates[i.val]).args.length (hA i) a)
            ((finCongr (two_mul n)).symm (Fin.natAdd n t)))))) := rfl

/-- Every retained shift coordinate reads its exact original tape bit, including
unused gates and argument positions and the zero-width case. -/
theorem equiv_shift {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S)
    (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (t : Fin 2) :
    (equiv C S n hA hS r).1.1 i t =
      (List.ofFn r).getD (10 * S * n + 2 * i + t) false := by
  rw [equiv_eq C S n hA hS (gateBound C S hS)]
  exact CoinRelabel.blocksEquiv_shift S n r i t

/-- Each extracted real key bit reads the exact original key tape address. -/
theorem equiv_key {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S)
    (r : Fin (10 * S * n + 2 * S) → Bool) (w : Fin C.size) (b : Bool) (t : Fin n) :
    (equiv C S n hA hS r).2.1 w b t =
      (List.ofFn r).getD ((b.toNat * S + w) * n + t) false := by
  rw [equiv_eq C S n hA hS (gateBound C S hS)]
  exact CoinRelabel.blocksEquiv_key S n r b (Fin.castLE hS w) t

/-- The extracted first nonce half reads the original row's first-width tape bits. -/
theorem equiv_nonce_first {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S)
    (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin C.gates.length)
    (a : Fin (C.gates[i.val]).args.length → Bool) (t : Fin n) :
    ((equiv C S n hA hS r).2.2 i a).1 t =
      (List.ofFn r).getD (2 * S * n + (4 * i +
        (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t) false := by
  rw [equiv_eq C S n hA hS (gateBound C S hS)]
  have h := CoinRelabel.blocksEquiv_row S n r (Fin.castLE (gateBound C S hS) i)
    (CoinSeedRelabel.assignmentEmbedding (C.gates[i.val]).args.length (hA i) a)
    ((finCongr (two_mul n)).symm (Fin.castAdd n t))
  rw [CoinSeedRelabel.assignmentEmbedding_eq] at h
  exact h

/-- The extracted second nonce half reads the original row's second-width tape bits. -/
theorem equiv_nonce_second {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S)
    (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin C.gates.length)
    (a : Fin (C.gates[i.val]).args.length → Bool) (t : Fin n) :
    ((equiv C S n hA hS r).2.2 i a).2 t =
      (List.ofFn r).getD (2 * S * n + (4 * i +
        (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + n + t) false := by
  rw [equiv_eq C S n hA hS (gateBound C S hS)]
  have h := CoinRelabel.blocksEquiv_row S n r (Fin.castLE (gateBound C S hS) i)
    (CoinSeedRelabel.assignmentEmbedding (C.gates[i.val]).args.length (hA i) a)
    ((finCongr (two_mul n)).symm (Fin.natAdd n t))
  rw [CoinSeedRelabel.assignmentEmbedding_eq] at h
  simpa only [Nat.add_assoc] using h

/-- Each unused key block is retained verbatim in the unchanged parameter. -/
theorem equiv_unused_key {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S)
    (r : Fin (10 * S * n + 2 * S) → Bool)
    (x : {x : Bool × Fin S // x ∉ Set.range (keyEmbedding C S hS)}) (t : Fin n) :
    (equiv C S n hA hS r).1.2.1 x t =
      (List.ofFn r).getD ((x.1.1.toNat * S + x.1.2) * n + t) false := by
  rw [equiv_eq C S n hA hS (gateBound C S hS)]
  exact CoinRelabel.blocksEquiv_key S n r x.1.1 x.1.2 t

/-- Each unused row block, including unused assignment codes, is retained verbatim. -/
theorem equiv_unused_row {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S)
    (r : Fin (10 * S * n + 2 * S) → Bool)
    (x : {x : Fin S × Fin 4 // x ∉ Set.range (rowEmbedding C S hA hS)})
    (t : Fin (2 * n)) :
    (equiv C S n hA hS r).1.2.2 x t =
      (List.ofFn r).getD (2 * S * n + (4 * x.1.1 + x.1.2) * (2 * n) + t) false := by
  rw [equiv_eq C S n hA hS (gateBound C S hS)]
  exact CoinRelabel.blocksEquiv_row S n r x.1.1 x.1.2 t

/-- The actual assignment permutation XORs each argument with its retained
shift bit. It depends only on `Rest`, not on the extracted value table.
[PS10, Theorem 163.7] -/
def permutation {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S)
    (p : Rest C S n hA hS) (i : Fin C.gates.length) :
    Equiv.Perm (Fin (C.gates[i.val]).args.length → Bool) :=
  xorPerm (fun t => p.1 (Fin.castLE (gateBound C S hS) i) (Fin.castLE (hA i) t))

/-- `permutation ... p i` is `xorPerm` of the retained argument-shift bits. -/
theorem permutation_eq {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S)
    (hG : C.gates.length ≤ S) (p : Rest C S n hA hS) (i : Fin C.gates.length) :
    permutation C S n hA hS p i =
      xorPerm (fun t => p.1 (Fin.castLE hG i) (Fin.castLE (hA i) t)) := rfl

/-- At every argument position, the derived permutation XORs the supplied
assignment bit with exactly that retained shift bit. -/
theorem permutation_apply {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S)
    (hG : C.gates.length ≤ S) (p : Rest C S n hA hS) (i : Fin C.gates.length)
    (a : Fin (C.gates[i.val]).args.length → Bool) (t : Fin (C.gates[i.val]).args.length) :
    permutation C S n hA hS p i a t =
      xor (a t) (p.1 (Fin.castLE hG i) (Fin.castLE (hA i) t)) := by
  simp only [permutation_eq C S n hA hS hG, xorPerm_apply]

/-- A seed whose permutation reader XORs the addressed shift bits has exactly
the permutation derived from the retained tape parameter. No distribution over
all permutations is asserted. [PS10, Theorem 163.7]

**Proof sketch.** Compare each assignment position. The seed reader and the
retained-shift reader give the same bit address; the finite cast reader removes
the padded index casts. -/
theorem seed_perm {m : ℕ} {ρ : Type} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S)
    (seed : List Bool → GarbleSeed C (Fin n → Bool) ρ)
    (hP : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i.val]).args.length → Bool)
        (t : Fin (C.gates[i.val]).args.length),
      (seed q).2.2 i a t = xor (a t) (q.getD (10 * S * n + 2 * i + t) false))
    (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin C.gates.length)
    (a : Fin (C.gates[i.val]).args.length → Bool) :
    (seed (List.ofFn r)).2.2 i a =
      permutation C S n hA hS (equiv C S n hA hS r).1 i a := by
  funext t
  rw [hP, permutation_apply C S n hA hS (gateBound C S hS), equiv_shift]
  simp only [Fin.coe_castLE]

section Seed

variable {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
  (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S)
  (seed : List Bool → GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (hK : ∀ q (w : Fin C.size) b (t : Fin n),
    (seed q).1 w b t = q.getD ((b.toNat * S + w) * n + t) false)
  (hR₀ : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i.val]).args.length → Bool)
      (t : Fin n),
    ((seed q).2.1 i a).1 t = q.getD (2 * S * n + (4 * i +
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t) false)
  (hR₁ : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i.val]).args.length → Bool)
      (t : Fin n),
    ((seed q).2.1 i a).2 t = q.getD (2 * S * n + (4 * i +
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + n + t) false)
  (hP : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i.val]).args.length → Bool)
      (t : Fin (C.gates[i.val]).args.length),
    (seed q).2.2 i a t = xor (a t) (q.getD (10 * S * n + 2 * i + t) false))

include hK hR₀ hR₁ hP

/-- A seed with the four addressed readers is exactly the extracted actual
key/nonce tables together with the permutation derived from retained shifts.
No actual sampler is defined here. [PS10, Theorem 163.7]

**Proof sketch.** Compare keys coordinate by coordinate using the key-address
reader. Compare each nonce pair using the two half-address readers. Finally,
compare assignment permutations pointwise with the retained-shift identity.
These equalities determine the three components of the existing seed. -/
theorem seed_eq (r : Fin (10 * S * n + 2 * S) → Bool) :
    seed (List.ofFn r) =
      ((equiv C S n hA hS r).2.1, (equiv C S n hA hS r).2.2,
        permutation C S n hA hS (equiv C S n hA hS r).1) := by
  apply Prod.ext
  · funext w b t
    rw [hK, equiv_key]
  · apply Prod.ext
    · funext i a
      apply Prod.ext
      · funext t
        rw [hR₀, equiv_nonce_first]
      · funext t
        rw [hR₁, equiv_nonce_second]
    · funext i
      apply Equiv.ext
      intro a
      exact seed_perm C S n hA hS seed hP r i a

/-- On the inverse tape encoded by a retained parameter and actual value table,
the supplied seed has exactly those keys/nonces and the parameter's derived
permutation. This is the concrete sampler identification used by coordinate fill.
[PS10, Theorem 163.7] -/
theorem seed_on_inverse (p : Rest C S n hA hS)
    (d : (Fin C.size → Bool → Fin n → Bool) ×
      ((i : Fin C.gates.length) → (Fin (C.gates[i.val]).args.length → Bool) →
        (Fin n → Bool) × (Fin n → Bool))) :
    seed (List.ofFn ((equiv C S n hA hS).symm (p, d))) =
      (d.1, d.2, permutation C S n hA hS p) := by
  have h := seed_eq C S n hA hS seed hK hR₀ hR₁ hP ((equiv C S n hA hS).symm (p, d))
  rw [Equiv.apply_symm_apply] at h
  exact h

end Seed

/-- A padded key coordinate at vertex `w ≥ C.size` is outside the actual-key
embedding image and therefore belongs to the retained parameter. -/
theorem key_not_mem_range {m : ℕ} (C : DAGCircuit m) (S : ℕ) (hS : C.size ≤ S)
    (w : Fin S) (b : Bool) (hw : C.size ≤ (w : ℕ)) :
    (b, w) ∉ Set.range (keyEmbedding C S hS) := by
  rintro ⟨⟨w', b'⟩, h⟩
  have hval : (w' : ℕ) = (w : ℕ) := by
    simpa only [keyEmbedding_eq, Fin.coe_castLE] using
      congrArg (fun x : Bool × Fin S => (x.2 : ℕ)) h
  have := w'.isLt
  omega

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues
