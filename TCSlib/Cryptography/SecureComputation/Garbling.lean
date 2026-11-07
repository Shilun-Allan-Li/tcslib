/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.CircuitComplexity.DAGCircuit
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Perm
import TCSlib.Cryptography.Foundations.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Garbled circuits (statement phase)

[PS10, §6.2.1–6.2.3]. Construction 158.a (inventory): to garble a circuit `C` with fan-in two,
associate two random keys `k_w^0, k_w^1` to every wire `w`. Each gate becomes a table with one
row per assignment of its input bits; the row encrypts the key of the gate's output value under
the keys of its inputs. The rows are randomly permuted, so the position of the row that
decrypts does not reveal the inputs. Claim 159.a (inventory): given the input keys, evaluating
the garbled circuit opens exactly one row per gate, with high probability, and ends with the key
of `C(x)` on the output wire.

**The construction on `main`'s circuits** (route note `design/S3b-yao-runWith.md`).
- The circuit is `main`'s `BoolCircuit.DAGCircuit`, with vertices numbered topologically.
- Garbled evaluation is a second instance of `DAGCircuit.runWith`, whose gate function reads its
  vertex from the length of the data so far.
- Its correctness is the simulation lemma `runWith_sim` (proved; the route probe's lemma), which
  relates the two runs through the wire keys.

**The encryption, abstracted.** The rows are built and opened through an interface `MultiEnc`:
encryption and decryption under a list of keys. A row with two inputs is doubly encrypted, one
with a single input singly encrypted, and a constant gate's row is in the clear. Its two
properties:
- `MultiEnc.DecCorrect`: decryption inverts encryption;
- `MultiEnc.WrongKeyBot δ`: under independent uniform keys, a row decrypted with a different key
  list gives `⊥` except with probability `δ`. This is [PS10]'s "the extra property" (§6.2.2).

The special encryption scheme of Algorithm 157.2 gives both, nested (`GarblingSpecial.lean`).

**Deviations.**
- **Gates of any fan-in up to two.** Each table has `2^{|args|} ∈ {1, 2, 4}` rows (`¬` gates and
  constant gates included); [PS10] describes the two-input case.
- **The row order.** A table lists its rows in a fixed enumeration of the assignments, composed
  with the gate's random permutation.
- **The evaluator** opens the first row that decrypts (`List.findSome?`).

## Main definitions

* `SecureComputation.MultiEnc`, `MultiEnc.DecCorrect`, `MultiEnc.WrongKeyBot`.
* `SecureComputation.gateOut`: a gate's output on an assignment of its argument positions.
* `SecureComputation.GarbleSeed`, `garbledTable`, `inputKeys`, `garbledValues`,
  `garbledOutput`: Construction 158.a and its evaluation.
* `SecureComputation.Good`: every table opens, under every assignment's keys, to the right key.

## Main results

* `SecureComputation.runWith_sim` (proved): two `runWith` runs agree through a per-vertex
  encoding.
* `SecureComputation.garbledValues_getD`, `garbledOutput_eq` (Claim 159.a, deterministic part,
  proved): a good garbling evaluates to the keys of the circuit's values, and of `C(x)`.
* `SecureComputation.uprob_not_good_le` (Claim 159.a, probabilistic part, stated; a `sorry` under
  a sketch): a garbling is good except with probability `12 · |gates| · δ`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.1–6.2.3 (book pp. 156–160).
-/

namespace TCSlib.Cryptography.SecureComputation

open BoolCircuit TCSlib.Cryptography

/-! ### Simulation of `runWith` -/

/-- **Indexed simulation of `runWith`.** If the second evaluator, at gate `i`, maps data that
encode the first evaluator's data (vertex by vertex, through `W v`) on the gate's inputs to the
encoding of the first evaluator's output, then the two runs agree through `W` at every
vertex.

**Proof sketch.** Use strong induction on the vertex number. At an input vertex, the claim is
the initial correspondence. At a gate vertex, both runs read their inputs from the preceding
prefix, whose length identifies this gate's vertex. Acyclicity puts every argument at a smaller
vertex, so the induction hypothesis relates the two argument lists. Reading an earlier vertex
is unchanged by the later gates; the gate simulation hypothesis therefore gives the required
correspondence for the newly appended value. -/
theorem runWith_sim {α β : Type} (fA : DAGGate → List α → α) (fB : ℕ → DAGGate → List β → β)
    (W : ℕ → α → β) (dA : α) (dB : β) (gs : List DAGGate) (initA : List α) (initB : List β)
    (hlen : initB.length = initA.length)
    (hinit : ∀ v < initA.length, initB.getD v dB = W v (initA.getD v dA))
    (hacyc : ∀ (i : ℕ) (h : i < gs.length), ∀ a ∈ (gs[i]).args, a < initA.length + i)
    (hgate : ∀ (i : ℕ) (h : i < gs.length) (vA : List α) (vB : List β),
       vA.length = initA.length + i → vB.length = initA.length + i →
       (∀ a ∈ (gs[i]).args, vB.getD a dB = W a (vA.getD a dA)) →
       fB (initA.length + i) gs[i] vB = W (initA.length + i) (fA gs[i] vA)) :
    ∀ v < initA.length + gs.length,
      (runWith (fun g vs => fB vs.length g vs) gs initB).getD v dB =
        W v ((runWith fA gs initA).getD v dA) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv
    by_cases hlt : v < initA.length
    · rw [runWith_getD_of_lt _ _ _ (hlen ▸ hlt), runWith_getD_of_lt _ _ _ hlt]
      exact hinit v hlt
    · obtain ⟨i, rfl⟩ : ∃ i, v = initA.length + i := ⟨v - initA.length, by omega⟩
      have hi : i < gs.length := by omega
      have hB := runWith_getD_gate (fun g vs => fB vs.length g vs) gs initB hi dB
      have hA := runWith_getD_gate fA gs initA hi dA
      rw [hlen] at hB
      rw [hB, hA, length_runWith, List.length_take_of_le hi.le, hlen]
      refine hgate i hi _ _ (by rw [length_runWith, List.length_take_of_le hi.le])
        (by rw [length_runWith, List.length_take_of_le hi.le, hlen]) fun a ha => ?_
      have ha' := hacyc i hi a ha
      rw [runWith_getD_take _ gs initB hi.le (by omega),
        runWith_getD_take _ gs initA hi.le ha']
      exact ih a ha' (by omega)

/-! ### Multi-key encryption -/

/-- **Encryption under a list of keys**: `enc ks o r` encrypts the key `o` under the keys `ks`
with coins `r`, and `dec ks c` decrypts, with `none` for `⊥`. -/
structure MultiEnc (K C ρ : Type) where
  /-- Encryption under a list of keys. -/
  enc : List K → K → ρ → C
  /-- Decryption under a list of keys; `none` is `⊥`. -/
  dec : List K → C → Option K

namespace MultiEnc

variable {K C ρ : Type}

/-- **Correctness**: decryption under at most two keys inverts encryption under them. -/
def DecCorrect (M : MultiEnc K C ρ) : Prop :=
  ∀ ks : List K, ks.length ≤ 2 → ∀ (o : K) (r : ρ), M.dec ks (M.enc ks o r) = some o

/-- `DecCorrect M` holds exactly when decryption inverts encryption under every list of at
most two keys, for every plaintext key and coin. -/
theorem decCorrect_iff (M : MultiEnc K C ρ) :
    M.DecCorrect ↔
      ∀ ks : List K, ks.length ≤ 2 → ∀ (o : K) (r : ρ),
        M.dec ks (M.enc ks o r) = some o := Iff.rfl

/-- **The wrong-key property with error `δ`** [PS10, §6.2.2, "the extra property"]: for at most
two positions, two independent uniform keys per position, and two different choices `a ≠ a'` of
key per position, a ciphertext of any key `o` under the `a`-keys decrypts to `⊥` under the
`a'`-keys, except with probability `δ` over the keys and the coins. -/
def WrongKeyBot [Fintype K] [Fintype ρ] (M : MultiEnc K C ρ) (δ : ℝ) : Prop :=
  ∀ (len : ℕ), len ≤ 2 → ∀ (a a' : Fin len → Bool), a ≠ a' → ∀ o : K,
    uprob (fun t : (Fin len → Bool → K) × ρ =>
      (M.dec (List.ofFn fun j => t.1 j (a' j))
        (M.enc (List.ofFn fun j => t.1 j (a j)) o t.2)).isSome = true) ≤ δ

/-- `WrongKeyBot M δ` holds exactly when each pair of distinct assignments to at most two
key positions gives successful wrong-key decryption probability at most `δ`, uniformly in
the plaintext key, with independent uniform key pairs and coins. -/
theorem wrongKeyBot_iff [Fintype K] [Fintype ρ] (M : MultiEnc K C ρ) (δ : ℝ) :
    M.WrongKeyBot δ ↔
      ∀ (len : ℕ), len ≤ 2 → ∀ (a a' : Fin len → Bool), a ≠ a' → ∀ o : K,
        uprob (fun t : (Fin len → Bool → K) × ρ =>
          (M.dec (List.ofFn fun j => t.1 j (a' j))
            (M.enc (List.ofFn fun j => t.1 j (a j)) o t.2)).isSome = true) ≤ δ := Iff.rfl

end MultiEnc

/-! ### Gates on assignments -/

/-- **A gate's output on an assignment of its argument positions**: the gate's kind applied to
the bits `ass 0, …, ass (|args| − 1)`. -/
def gateOut (g : DAGGate) (ass : Fin g.args.length → Bool) : Bool :=
  (DAGGate.mk g.kind (List.range g.args.length)).eval (List.ofFn ass)

/-- On any assignment of argument positions, `gateOut` evaluates the gate's kind on the
assignment list, with arguments replaced by their consecutive positions. -/
theorem gateOut_eq_eval (g : DAGGate) (ass : Fin g.args.length → Bool) :
    gateOut g ass =
      (DAGGate.mk g.kind (List.range g.args.length)).eval (List.ofFn ass) := rfl

/-- Reading a list of values at a gate's arguments is the `ofFn` of the positions. -/
theorem map_args_eq_ofFn {β : Type} (g : DAGGate) (f : ℕ → β) :
    g.args.map f = List.ofFn fun t : Fin g.args.length => f (g.args[t]) := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp

/-- The range positions read the assignment back. -/
private theorem map_range_getD_ofFn {len : ℕ} (ass : Fin len → Bool) :
    (List.range len).map (fun a => (List.ofFn ass).getD a false) = List.ofFn ass := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ (by simpa using h₂)]
  simp

/-- **The assignment read from the circuit's values gives the gate's value**: `gateOut` at the
bits of the arguments is `DAGGate.eval`. -/
theorem gateOut_eq (g : DAGGate) (vals : List Bool) :
    gateOut g (fun t => vals.getD (g.args[t]) false) = g.eval vals := by
  have hA := map_range_getD_ofFn (fun t : Fin g.args.length => vals.getD (g.args[t]) false)
  have hB := map_args_eq_ofFn g (fun a => vals.getD a false)
  have hall : ∀ (l : List ℕ) (p : ℕ → Bool), l.all p = (l.map p).all id := by
    intro l p; rw [List.all_map]; rfl
  have hany : ∀ (l : List ℕ) (p : ℕ → Bool), l.any p = (l.map p).any id := by
    intro l p; rw [List.any_map]; rfl
  unfold gateOut
  rw [DAGGate.eval_eq]
  cases g.kind <;> simp only [hall, hany, hA, hB]

/-! ### The garbling -/

variable {K C ρ : Type} [Inhabited K] {n : ℕ}

/-- **The randomness of a garbling** of `Cc`: two keys per vertex, a coin per table row, and a
permutation of each gate's rows. -/
abbrev GarbleSeed (Cc : DAGCircuit n) (K ρ : Type) : Type :=
  (Fin Cc.size → Bool → K) ×
    ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ) ×
    ((i : Fin Cc.gates.length) → Equiv.Perm (Fin (Cc.gates[i]).args.length → Bool))

/-- A garbling seed is the product of the two-key function at each vertex, the coin function
for each gate assignment, and the row permutation at each gate. -/
theorem GarbleSeed_eq (Cc : DAGCircuit n) (K ρ : Type) :
    GarbleSeed Cc K ρ =
      ((Fin Cc.size → Bool → K) ×
        ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ) ×
        ((i : Fin Cc.gates.length) → Equiv.Perm (Fin (Cc.gates[i]).args.length → Bool))) := rfl

variable (M : MultiEnc K C ρ) (Cc : DAGCircuit n)

/-- The key of vertex `v` for the bit `b` (a default beyond the circuit). -/
def keyAt (s : GarbleSeed Cc K ρ) (v : ℕ) (b : Bool) : K :=
  if h : v < Cc.size then s.1 ⟨v, h⟩ b else default

/-- The key at `v` for bit `b` is the seed's key when `v < Cc.size`, and `default` otherwise. -/
theorem keyAt_eq (s : GarbleSeed Cc K ρ) (v : ℕ) (b : Bool) :
    keyAt Cc s v b = if h : v < Cc.size then s.1 ⟨v, h⟩ b else default := rfl

/-- The keys of gate `i`'s arguments under the assignment `a` of its positions. -/
def argKeys (s : GarbleSeed Cc K ρ) (i : Fin Cc.gates.length)
    (a : Fin (Cc.gates[i]).args.length → Bool) : List K :=
  List.ofFn fun t => keyAt Cc s ((Cc.gates[i]).args[t]) (a t)

/-- The argument-key list of gate `i` enumerates the wire key selected by `a t` at each
argument vertex `(Cc.gates[i]).args[t]`. -/
theorem argKeys_eq (s : GarbleSeed Cc K ρ) (i : Fin Cc.gates.length)
    (a : Fin (Cc.gates[i]).args.length → Bool) :
    argKeys Cc s i a = List.ofFn fun t => keyAt Cc s ((Cc.gates[i]).args[t]) (a t) := rfl

/-- **The row of gate `i` for the assignment `a`** [PS10, §6.2.3]: the key of the gate's output
on `a`, encrypted under the keys of its arguments on `a`. -/
def garbledRow (s : GarbleSeed Cc K ρ) (i : Fin Cc.gates.length)
    (a : Fin (Cc.gates[i]).args.length → Bool) : C :=
  M.enc (argKeys Cc s i a) (keyAt Cc s (n + i) (gateOut (Cc.gates[i]) a)) (s.2.1 i a)

/-- A garbled row encrypts the output wire key for `gateOut (Cc.gates[i]) a` under
`argKeys Cc s i a`, using that row's seed coins. -/
theorem garbledRow_eq (s : GarbleSeed Cc K ρ) (i : Fin Cc.gates.length)
    (a : Fin (Cc.gates[i]).args.length → Bool) :
    garbledRow M Cc s i a =
      M.enc (argKeys Cc s i a) (keyAt Cc s (n + i) (gateOut (Cc.gates[i]) a)) (s.2.1 i a) := rfl

/-- **The garbled table of gate `i`** [PS10, §6.2.3, "the rows … must be randomly shuffled"]: the
rows in a fixed enumeration of the assignments, composed with the gate's random permutation. -/
noncomputable def garbledTable (s : GarbleSeed Cc K ρ) (i : Fin Cc.gates.length) : List C :=
  (Finset.univ : Finset (Fin (Cc.gates[i]).args.length → Bool)).toList.map
    fun a => garbledRow M Cc s i (s.2.2 i a)

/-- Gate `i`'s table enumerates its assignments through `Finset.univ.toList` and applies the
seed's permutation before forming each garbled row. -/
theorem garbledTable_eq (s : GarbleSeed Cc K ρ) (i : Fin Cc.gates.length) :
    garbledTable M Cc s i =
      (Finset.univ : Finset (Fin (Cc.gates[i]).args.length → Bool)).toList.map
        fun a => garbledRow M Cc s i (s.2.2 i a) := rfl

/-- The garbled table at vertex `v` (none at the inputs). -/
noncomputable def tableAt (s : GarbleSeed Cc K ρ) (v : ℕ) : List C :=
  if h : n ≤ v ∧ v - n < Cc.gates.length then garbledTable M Cc s ⟨v - n, h.2⟩ else []

/-- The table at `v` is gate `v - n`'s garbled table when `v` names a gate vertex, and is
empty otherwise, including input vertices and vertices beyond the circuit. -/
theorem tableAt_eq (s : GarbleSeed Cc K ρ) (v : ℕ) :
    tableAt M Cc s v = if h : n ≤ v ∧ v - n < Cc.gates.length then
      garbledTable M Cc s ⟨v - n, h.2⟩ else [] := rfl

/-- The table at the vertex of gate `i` is its garbled table. -/
theorem tableAt_gate (s : GarbleSeed Cc K ρ) {i : ℕ} (hi : i < Cc.gates.length) :
    tableAt M Cc s (n + i) = garbledTable M Cc s ⟨i, hi⟩ := by
  unfold tableAt
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1
  exact Fin.ext (by simp)

/-- **The evaluator at a gate** [PS10, §6.2.3, "the evaluating player can attempt to decrypt all
four rows"]: the first row of the vertex's table that decrypts under the keys of the gate's
arguments (a default if none does). -/
def evalGate (T : ℕ → List C) (v : ℕ) (g : DAGGate) (vs : List K) : K :=
  ((T v).findSome? (M.dec (g.args.map fun a => vs.getD a default))).getD default

/-- Evaluating gate `g` at `v` decrypts the first successful row of `T v` under its argument
keys from `vs`, with `default` when no row decrypts. -/
theorem evalGate_eq (T : ℕ → List C) (v : ℕ) (g : DAGGate) (vs : List K) :
    evalGate M T v g vs =
      ((T v).findSome? (M.dec (g.args.map fun a => vs.getD a default))).getD default := rfl

/-- **The input keys**: the key of each input bit of `x`. -/
def inputKeys (s : GarbleSeed Cc K ρ) (x : Fin n → Bool) : List K :=
  List.ofFn fun i : Fin n => keyAt Cc s i (x i)

/-- The input-key list enumerates `keyAt Cc s i (x i)` over all input positions `i`. -/
theorem inputKeys_eq (s : GarbleSeed Cc K ρ) (x : Fin n → Bool) :
    inputKeys Cc s x = List.ofFn fun i : Fin n => keyAt Cc s i (x i) := rfl

/-- **Garbled evaluation**: `runWith` over the circuit's gates from the input keys, each gate
opened by `evalGate` at its vertex. -/
noncomputable def garbledValues (s : GarbleSeed Cc K ρ) (init : List K) : List K :=
  runWith (fun g vs => evalGate M (tableAt M Cc s) vs.length g vs) Cc.gates init

/-- Garbled evaluation runs `runWith` from `init` over `Cc.gates`, opening each gate at the
vertex given by the current value-list length. -/
theorem garbledValues_eq (s : GarbleSeed Cc K ρ) (init : List K) :
    garbledValues M Cc s init =
      runWith (fun g vs => evalGate M (tableAt M Cc s) vs.length g vs) Cc.gates init := rfl

/-- **The garbled output** on input `x`: the key reached at the output vertex. -/
noncomputable def garbledOutput (s : GarbleSeed Cc K ρ) (x : Fin n → Bool) : K :=
  (garbledValues M Cc s (inputKeys Cc s x)).getD Cc.output default

/-- The garbled output reads the value at `Cc.output` after garbled evaluation from the
input keys, using `default` for a missing value. -/
theorem garbledOutput_eq_getD (s : GarbleSeed Cc K ρ) (x : Fin n → Bool) :
    garbledOutput M Cc s x =
      (garbledValues M Cc s (inputKeys Cc s x)).getD Cc.output default := rfl

/-- **A good garbling**: at every gate, under the keys of every assignment of its arguments, the
first row of the table that decrypts gives the key of the gate's output on that assignment. -/
def Good (s : GarbleSeed Cc K ρ) : Prop :=
  ∀ (i : Fin Cc.gates.length) (a : Fin (Cc.gates[i]).args.length → Bool),
    (garbledTable M Cc s i).findSome? (M.dec (argKeys Cc s i a)) =
      some (keyAt Cc s (n + i) (gateOut (Cc.gates[i]) a))

/-- `Good M Cc s` holds exactly when every gate table, under every assignment's argument
keys, first decrypts to the key of that gate's output on the assignment. -/
theorem good_iff (s : GarbleSeed Cc K ρ) :
    Good M Cc s ↔
      ∀ (i : Fin Cc.gates.length) (a : Fin (Cc.gates[i]).args.length → Bool),
        (garbledTable M Cc s i).findSome? (M.dec (argKeys Cc s i a)) =
          some (keyAt Cc s (n + i) (gateOut (Cc.gates[i]) a)) := Iff.rfl

/-- **Claim 159.a, deterministic part: a good garbling evaluates to the keys of the circuit's
values** [PS10, §6.2.3]: at every vertex, garbled evaluation from the input keys of `x` reaches
the key of the vertex's value on `x` (`runWith_sim`, with the encoding `keyAt`).

**Proof sketch.** Apply indexed simulation with each Boolean wire value encoded by its
corresponding wire key. The input-key list gives the initial correspondence, and the circuit's
topological ordering supplies acyclicity. At a gate, the correspondence on its arguments makes
the supplied keys exactly those for their Boolean assignment. Goodness says that the first
decrypting row returns the key of this assignment's output. The Boolean gate equation identifies
that output with the value in the ordinary circuit run, completing the simulation. -/
theorem garbledValues_getD (s : GarbleSeed Cc K ρ) (hgood : Good M Cc s) (x : Fin n → Bool) :
    ∀ v < Cc.size, (garbledValues M Cc s (inputKeys Cc s x)).getD v default =
      keyAt Cc s v ((Cc.values x).getD v false) := by
  intro v hv
  have hlenA : (List.ofFn x).length = n := List.length_ofFn
  refine runWith_sim DAGGate.eval (fun v g vs => evalGate M (tableAt M Cc s) v g vs)
    (keyAt Cc s) false default Cc.gates (List.ofFn x) (inputKeys Cc s x)
    (by simp [inputKeys]) ?_ ?_ ?_ v (by rw [hlenA]; exact hv)
  · intro w hw
    rw [hlenA] at hw
    have h1 : w < (inputKeys Cc s x).length := by simp [inputKeys, hw]
    have h2 : w < (List.ofFn x).length := by simp [hw]
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
    simp [inputKeys]
  · intro i hi a ha
    rw [hlenA]
    exact Cc.args_lt i hi a ha
  · intro i hi vA vB _ _ hargs
    rw [hlenA]
    show evalGate M (tableAt M Cc s) (n + i) (Cc.gates[i]) vB = _
    simp only [evalGate]
    rw [tableAt_gate M Cc s hi]
    have hkeys : (Cc.gates[i]).args.map (fun a => vB.getD a default) =
        argKeys Cc s ⟨i, hi⟩ (fun t => vA.getD ((Cc.gates[i]).args[t]) false) := by
      rw [List.map_congr_left hargs, map_args_eq_ofFn]
      rfl
    rw [hkeys, hgood ⟨i, hi⟩]
    simp only [Option.getD_some]
    exact congrArg (keyAt Cc s (n + i)) (gateOut_eq (Cc.gates[i]) vA)

/-- **Claim 159.a, deterministic part, at the output**: a good garbling's output on `x` is the
key of `C(x)` on the output wire. -/
theorem garbledOutput_eq (s : GarbleSeed Cc K ρ) (hgood : Good M Cc s) (x : Fin n → Bool) :
    garbledOutput M Cc s x = keyAt Cc s Cc.output (Cc.eval x) :=
  garbledValues_getD M Cc s hgood x Cc.output Cc.output_lt

/-- **Claim 159.a, probabilistic part: a garbling is good with high probability** [PS10, §6.2.3,
"all but one row will evaluate to `⊥`"]: for a fan-in-two circuit and a multi-key encryption
that is correct and has the wrong-key property with error `δ`, a uniformly random garbling fails
to be good with probability at most `12 · |gates| · δ`.

**Proof sketch.** Fix a gate `i` and an assignment `a`.
1. By correctness, the row of `a` decrypts under `a`'s keys to the right key. So `Good` can fail
   at `(i, a)` only if another row, of an assignment `a'' ≠ a`, decrypts under `a`'s keys.
2. The arguments are distinct vertices (`IsWellFormed`: no duplicates), and they precede the
   gate's own vertex. So the keys of the argument positions are independent uniform pairs, and
   the plaintext key and the row's coin are independent of them. By `WrongKeyBot`, averaged over
   the plaintext and the coin, that event has probability at most `δ`.
3. A gate has at most `2^2 = 4` assignments and `3` other rows each: at most `12` events per gate.
   The union bound over the gates gives `12 · |gates| · δ`. The permutations play no role in
   correctness. -/
theorem uprob_not_good_le [Fintype K] [Fintype ρ] (hdec : M.DecCorrect) {δ : ℝ}
    (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo) :
    uprob (fun s : GarbleSeed Cc K ρ => ¬ Good M Cc s) ≤ 12 * Cc.gates.length * δ := by
  sorry

end TCSlib.Cryptography.SecureComputation
