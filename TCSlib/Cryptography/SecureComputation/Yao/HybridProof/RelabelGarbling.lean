/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Garbling
import TCSlib.Cryptography.Foundations.BitLists

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Seed-by-seed relabeling of a generic garbling

A wire-value map relabels each wire's two keys, XORs argument assignments,
readdresses row coins and composes the row permutation with that XOR. The
original table then has an exact expression in the new seed: its output bit
is the old gate truth table on the XORed assignment, XOR the output-wire value.
The statements are generic in the multi-key encryption interface and include
arbitrary gate arities and default keys outside the circuit.

## Main definitions

* `argValues`: the wire-value map restricted to a gate's argument positions.
* `relabelSeed`: relabel keys, row coins and row permutations by these values.

## Main results

* `keyAt_relabel`, `argKeys_relabel`: exact key-selection equations.
* `garbledTable_relabel`: the same enumerated table expressed through the relabeled seed.
* `inputKeys_relabel`, `output_pair_relabel`: input keys and swapped decoding pairs.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 163.7 (the garbling hybrid).
* [LP09] Y. Lindell, B. Pinkas, *A proof of security of Yao's protocol for
  two-party computation*, Journal of Cryptology 22(2), 2009, pp. 161–188.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling

open BoolCircuit TCSlib.Cryptography

/-- Restrict a wire-value map `v` to the argument positions of gate `i`:
`argValues C v i t = v (C.gates[i].args[t])`. -/
def argValues {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool) (i : Fin C.gates.length) :
    Fin (C.gates[i]).args.length → Bool :=
  fun t => v ((C.gates[i]).args[t])

/-- `argValues C v i = (fun t => v (C.gates[i].args[t]))`. -/
theorem argValues_eq {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    (i : Fin C.gates.length) :
    argValues C v i = fun t => v ((C.gates[i]).args[t]) := rfl

/-- Argument position `t` reads the wire value at `C.gates[i].args[t]`.
`argValues C v i t = v ((C.gates[i]).args[t])`. -/
theorem argValues_apply {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    (i : Fin C.gates.length) (t : Fin (C.gates[i]).args.length) :
    argValues C v i t = v ((C.gates[i]).args[t]) := rfl

/-- Relabel a garbling seed by wire values `v`: key choice `b` becomes `b XOR v w`,
row coins at assignment `a` come from `a XOR argValues`, and the row permutation
is composed with that same assignment XOR. [PS10, Theorem 163.7; LP09]
`relabelSeed C v s = ((fun w b => s.1 w (xor b (v w))), (fun i a => s.2.1 i (xorPerm (argValues C v
i) a)), fun i => (s.2.2 i).trans (xorPerm (argValues C v i)))`. -/
def relabelSeed {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool) {K ρ : Type}
    (s : GarbleSeed C K ρ) : GarbleSeed C K ρ :=
  ((fun w b => s.1 w (xor b (v w))),
    (fun i a => s.2.1 i (xorPerm (argValues C v i) a)),
    fun i => (s.2.2 i).trans (xorPerm (argValues C v i)))

/-- `relabelSeed C v s` is the tuple of choice-relabeled keys, XOR-addressed row
coins, and the row permutations composed with assignment XOR.
`relabelSeed C v s = ((fun w b => s.1 w (xor b (v w))), (fun i a => s.2.1 i (xorPerm (argValues C v
i) a)), fun i => (s.2.2 i).trans (xorPerm (argValues C v i)))`. -/
theorem relabelSeed_eq {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool) {K ρ : Type}
    (s : GarbleSeed C K ρ) :
    relabelSeed C v s =
      ((fun w b => s.1 w (xor b (v w))),
        (fun i a => s.2.1 i (xorPerm (argValues C v i) a)),
        fun i => (s.2.2 i).trans (xorPerm (argValues C v i))) := rfl

/-- The relabeled key at wire `w` and choice `b` is `s.1 w (b XOR v w)`.
`(relabelSeed C v s).1 w b = s.1 w (xor b (v w))`. -/
theorem relabelSeed_key {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool) {K ρ : Type}
    (s : GarbleSeed C K ρ) (w : Fin C.size) (b : Bool) :
    (relabelSeed C v s).1 w b = s.1 w (xor b (v w)) := rfl

/-- The relabeled row coin at `i,a` is the old coin at `i,a XOR argValues`.
`(relabelSeed C v s).2.1 i a = s.2.1 i (xorPerm (argValues C v i) a)`. -/
theorem relabelSeed_coin {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool) {K ρ : Type}
    (s : GarbleSeed C K ρ) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) :
    (relabelSeed C v s).2.1 i a = s.2.1 i (xorPerm (argValues C v i) a) := rfl

/-- The relabeled row permutation maps `a` to `s.2.2 i a XOR argValues`.
`(relabelSeed C v s).2.2 i a = xorPerm (argValues C v i) (s.2.2 i a)`. -/
theorem relabelSeed_perm {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool) {K ρ : Type}
    (s : GarbleSeed C K ρ) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) :
    (relabelSeed C v s).2.2 i a = xorPerm (argValues C v i) (s.2.2 i a) := rfl

/-- For every vertex `w`, including the default region outside `C.size`,
`keyAt C (relabelSeed C v s) w b = keyAt C s w (b XOR v w)`. -/
theorem keyAt_relabel {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    {K ρ : Type} [Inhabited K] (s : GarbleSeed C K ρ) (w : ℕ) (b : Bool) :
    keyAt C (relabelSeed C v s) w b = keyAt C s w (xor b (v w)) := by
  by_cases hw : w < C.size
  · simp only [keyAt_eq, dif_pos hw, relabelSeed_key]
  · simp only [keyAt_eq, dif_neg hw]

/-- The original choice `b` is choice `b XOR v w` in the relabeled seed:
`keyAt C s w b = keyAt C (relabelSeed C v s) w (b XOR v w)`. -/
theorem keyAt_original {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    {K ρ : Type} [Inhabited K] (s : GarbleSeed C K ρ) (w : ℕ) (b : Bool) :
    keyAt C s w b = keyAt C (relabelSeed C v s) w (xor b (v w)) := by
  rw [keyAt_relabel, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- Argument keys under the relabeled seed at assignment `a` are the original
argument keys at `a XOR argValues C v i`.
`argKeys C (relabelSeed C v s) i a = argKeys C s i (xorPerm (argValues C v i) a)`. -/
theorem argKeys_relabel {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    {K ρ : Type} [Inhabited K] (s : GarbleSeed C K ρ) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) :
    argKeys C (relabelSeed C v s) i a =
      argKeys C s i (xorPerm (argValues C v i) a) := by
  rw [argKeys_eq, argKeys_eq]
  apply congrArg List.ofFn
  funext t
  simp only [keyAt_relabel, xorPerm_apply, argValues_apply]

/-- Encrypting under the relabeled seed at `a`, with output bit
`gateOut (a XOR argValues) XOR v(output)`, is the original row at
`a XOR argValues`. This is pointwise in every key and row coin.
[PS10, Theorem 163.7; LP09]
`M.enc (argKeys C (relabelSeed C v s) i a) (keyAt C (relabelSeed C v s) (m + i) (xor (gateOut
(C.gates[i]) (xorPerm (argValues C v i) a)) (v (m + i)))) ((relabelSeed C v s).2.1 i a) = garbledRow
M C s i (xorPerm (argValues C v i) a)`. -/
theorem row_relabel {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    {K W ρ : Type} [Inhabited K] (M : MultiEnc K W ρ) (s : GarbleSeed C K ρ)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) :
    M.enc (argKeys C (relabelSeed C v s) i a)
        (keyAt C (relabelSeed C v s) (m + i)
          (xor (gateOut (C.gates[i]) (xorPerm (argValues C v i) a)) (v (m + i))))
        ((relabelSeed C v s).2.1 i a) =
      garbledRow M C s i (xorPerm (argValues C v i) a) := by
  rw [argKeys_relabel, keyAt_relabel, relabelSeed_coin, garbledRow_eq,
    Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The original garbled table is exactly the same enumerated list generated
from the relabeled seed, with plaintext bit
`gateOut (a XOR argValues) XOR v(output)`. No reordering of the enumeration
or probabilistic argument is needed. [PS10, Theorem 163.7; LP09]
`garbledTable M C s i = (Finset.univ : Finset (Fin (C.gates[i]).args.length → Bool)).toList.map (fun
a => let b := (relabelSeed C v s).2.2 i a; M.enc (argKeys C (relabelSeed C v s) i b) (keyAt C
(relabelSeed C v s) (m + i) (xor (gateOut (C.gates[i]) (xorPerm (argValues C v i) b)) (v (m + i))))
((relabelSeed C v s).2.1 i b))`.

**Proof sketch.** At each enumerated assignment, the new row permutation XORs
the old assignment with the argument values. The transformed-row identity
converts that ciphertext back to the old seed at a second XOR of those values.
The two XORs cancel pointwise, leaving exactly the original enumerated row. -/
theorem garbledTable_relabel {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    {K W ρ : Type} [Inhabited K] (M : MultiEnc K W ρ) (s : GarbleSeed C K ρ)
    (i : Fin C.gates.length) :
    garbledTable M C s i =
      (Finset.univ : Finset (Fin (C.gates[i]).args.length → Bool)).toList.map
        (fun a =>
          let b := (relabelSeed C v s).2.2 i a
          M.enc (argKeys C (relabelSeed C v s) i b)
            (keyAt C (relabelSeed C v s) (m + i)
              (xor (gateOut (C.gates[i]) (xorPerm (argValues C v i) b)) (v (m + i))))
            ((relabelSeed C v s).2.1 i b)) := by
  rw [garbledTable_eq]
  refine List.map_congr_left fun a _ => ?_
  dsimp only
  conv_rhs => rw [row_relabel]
  rw [relabelSeed_perm]
  apply congrArg (garbledRow M C s i)
  funext t
  simp only [xorPerm_apply, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The relabeled input-key list on `x` is the original input-key list on
`fun i => x i XOR v i`, for all input vertices. -/
theorem inputKeys_relabel {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    {K ρ : Type} [Inhabited K] (s : GarbleSeed C K ρ) (x : Fin m → Bool) :
    inputKeys C (relabelSeed C v s) x = inputKeys C s (fun i => xor (x i) (v i)) := by
  rw [inputKeys_eq, inputKeys_eq]
  apply congrArg List.ofFn
  funext i
  exact keyAt_relabel C v s i (x i)

/-- Any selected list of original wire keys is the selected list of relabeled
keys with choice `bits j XOR v (wire j)`. This includes subsets of input wires
and repeated selected wires.
`(List.ofFn fun j => keyAt C s (wire j) (bits j)) = (List.ofFn fun j => keyAt C (relabelSeed C v s)
(wire j) (xor (bits j) (v (wire j))))`. -/
theorem selectedKeys_original {m k : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    {K ρ : Type} [Inhabited K] (s : GarbleSeed C K ρ) (wire : Fin k → ℕ)
    (bits : Fin k → Bool) :
    (List.ofFn fun j => keyAt C s (wire j) (bits j)) =
      (List.ofFn fun j => keyAt C (relabelSeed C v s) (wire j)
        (xor (bits j) (v (wire j)))) := by
  apply congrArg List.ofFn
  funext j
  exact keyAt_original C v s (wire j) (bits j)

/-- The original output-key pair at `w` is the relabeled pair with its two
entries swapped exactly when `v w = true`. This also holds for default keys
outside `C.size`. -/
theorem output_pair_relabel {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    {K ρ : Type} [Inhabited K] (s : GarbleSeed C K ρ) (w : ℕ) :
    (keyAt C s w false, keyAt C s w true) =
      if v w then
        (keyAt C (relabelSeed C v s) w true, keyAt C (relabelSeed C v s) w false)
      else (keyAt C (relabelSeed C v s) w false, keyAt C (relabelSeed C v s) w true) := by
  cases hv : v w <;> simp [hv, keyAt_relabel]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling
