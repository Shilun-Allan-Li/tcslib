/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Foundations.BitLists
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut requested := 0
  let mut excluded := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let home := env.header.moduleNames[idx.toNat]!
      if home.toString.startsWith "TCSlib." then
        if let .defnInfo d := ci then
          let status ← liftCoreM <| Lean.getReducibilityStatus name
          let matcher := Lean.Meta.isMatcherCore env name
          let rec body : Nat → Expr → Expr
            | 0, e => e
            | fuel+1, .lam _ _ b _ => body fuel b
            | fuel+1, .letE _ _ v b _ => body fuel (b.instantiate1 v)
            | _, e => e
          let ty := d.type.getForallBody.getAppFn.constName?
          let val := body 64 d.value
          let coe := ty == some `CoeFun || ty == some `Coe
          let map := if val.getAppArgs.isEmpty then val else val.getAppArgs.back!
          let projection := match (body 64 map).getAppFn with
            | .proj .. => true
            | .const n _ => env.isProjectionFn n
            | _ => false
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && false) ||
            (true && coe && projection)
          if isNotation || (status == .reducible && !matcher) then
            excluded := excluded + 1
            logInfo m!"EXCLUDED\t{home}\t{name}"
          else
            let id := mkIdent name
            if status != .irreducible then
              elabCommand (← `(command| attribute [local irreducible] $id:ident))
            let installed ← liftCoreM <| Lean.getReducibilityStatus name
            unless installed == .irreducible do
              throwError "seal not installed: {name}"
            requested := requested + 1
            logInfo m!"SEALED\t{home}\t{name}"
  logInfo m!"SEAL_COUNTS requested={requested} excluded={excluded}"

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exact coin-block bijections for garbling

The tape of `10 S n + 2 S` bits consists of two `S`-by-`n` key tables,
`S`-by-four rows of `2 n` bits, and `S` two-bit shifts. The equivalences below
include zero-width key and row tables. Relabeling permutes key choices and row
blocks and XORs shift bits; callers can fix unused coordinates explicitly.

## Main definitions

* `Blocks`: the typed key, row and shift tables.
* `splitTape`: the three contiguous regions of the tape.
* `blocksEquiv`: the complete tape as its three typed tables.
* `relabel`: a coin bijection obtained by relabeling those tables.

## Main results

* `blocksEquiv_key`, `blocksEquiv_row`, `blocksEquiv_shift`: exact offset equations.
* `relabel_blocks`: conjugation through the typed block representation.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 163.7 (the coin relabeling in the garbling hybrid).
* [BMR90] D. Beaver, S. Micali, P. Rogaway, *The round complexity of secure
  protocols*, STOC 1990, pp.503–513 (point-and-permute).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel

open TCSlib.Cryptography

/-- `Blocks S n` is a key table `Bool → Fin S → Fin n → Bool`, a row table
`Fin S → Fin 4 → Fin (2 n) → Bool`, and shifts `Fin S → Fin 2 → Bool`. -/
abbrev Blocks (S n : ℕ) :=
  (Bool → Fin S → Fin n → Bool) ×
    (Fin S → Fin 4 → Fin (2 * n) → Bool) × (Fin S → Fin 2 → Bool)

/-- `Blocks S n` is the product of its key, row and shift function types. -/
theorem Blocks_eq (S n : ℕ) :
    Blocks S n = ((Bool → Fin S → Fin n → Bool) ×
      (Fin S → Fin 4 → Fin (2 * n) → Bool) × (Fin S → Fin 2 → Bool)) := rfl

/-- Split `10 S n + 2 S` coin bits into regions of lengths `2 S n`, `4 S (2 n)`
and `2 S`, by two append equivalences. Zero widths are included. -/
def splitTape (S n : ℕ) :
    (Fin (10 * S * n + 2 * S) → Bool) ≃
      (Fin ((2 * S) * n) → Bool) ×
        (Fin ((S * 4) * (2 * n)) → Bool) × (Fin (S * 2) → Bool) :=
  let h : 10 * S * n + 2 * S = (2 * S) * n + ((S * 4) * (2 * n) + S * 2) := by ring
  (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)).trans
    ((Fin.appendEquiv ((2 * S) * n) ((S * 4) * (2 * n) + S * 2)).symm.trans
      ((Equiv.refl _).prodCongr (Fin.appendEquiv ((S * 4) * (2 * n)) (S * 2)).symm))

/-- The key region of `splitTape S n r` reads the tape at its unchanged offset:
`(splitTape S n r).1 i = (ofFn r).getD i false`. -/
theorem splitTape_key (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool)
    (i : Fin ((2 * S) * n)) :
    (splitTape S n r).1 i = (List.ofFn r).getD i false := by
  have hsum : 10 * S * n + 2 * S = (2 * S) * n + ((S * 4) * (2 * n) + S * 2) := by
    ring
  have hi := i.isLt
  have hb : (i : ℕ) < 10 * S * n + 2 * S := by omega
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hb), List.getElem_ofFn]
  rfl

/-- The row region of `splitTape S n r` begins at `2 S n`:
`(splitTape S n r).2.1 i = (ofFn r).getD (2*S*n+i) false`. -/
theorem splitTape_row (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool)
    (i : Fin ((S * 4) * (2 * n))) :
    (splitTape S n r).2.1 i = (List.ofFn r).getD (2 * S * n + i) false := by
  have hsum : 10 * S * n + 2 * S = (2 * S) * n + ((S * 4) * (2 * n) + S * 2) := by
    ring
  have hi := i.isLt
  have hb : 2 * S * n + i < 10 * S * n + 2 * S := by omega
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hb), List.getElem_ofFn]
  rfl

/-- The shift region of `splitTape S n r` begins at `10 S n`:
`(splitTape S n r).2.2 i = (ofFn r).getD (10*S*n+i) false`. -/
theorem splitTape_shift (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool)
    (i : Fin (S * 2)) :
    (splitTape S n r).2.2 i = (List.ofFn r).getD (10 * S * n + i) false := by
  have hi := i.isLt
  have hb : 10 * S * n + i < 10 * S * n + 2 * S := by omega
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hb), List.getElem_ofFn]
  apply congrArg r
  apply Fin.ext
  change (2 * S) * n + ((S * 4) * (2 * n) + (i : ℕ)) = 10 * S * n + i
  ring

/-- `splitTape S n r` is the triple of windows at offsets `0`, `2 S n`, and
`10 S n`, of lengths `2 S n`, `4 S (2 n)`, and `2 S`, respectively. -/
theorem splitTape_eq (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool) :
    splitTape S n r =
      ((fun i : Fin ((2 * S) * n) => (List.ofFn r).getD i false),
        (fun i : Fin ((S * 4) * (2 * n)) => (List.ofFn r).getD (2 * S * n + i) false),
        (fun i : Fin (S * 2) => (List.ofFn r).getD (10 * S * n + i) false)) := by
  apply Prod.ext
  · funext i
    exact splitTape_key S n r i
  · apply Prod.ext
    · funext i
      exact splitTape_row S n r i
    · funext i
      exact splitTape_shift S n r i

/-- The complete tape of `10 S n + 2 S` bits is equivalent to its typed key, row,
and shift tables. The construction uses only splitting, existing block equivalences,
and reindexing; in particular it includes `S = 0` and `n = 0`.
[PS10, Theorem 163.7, coin relabeling] -/
def blocksEquiv (S n : ℕ) : (Fin (10 * S * n + 2 * S) → Bool) ≃ Blocks S n :=
  let eK : (Fin ((2 * S) * n) → Bool) ≃ (Bool → Fin S → Fin n → Bool) :=
    ((FunFamily.blocks (2 * S) n).trans (blocksEquivX 2 S (Fin n → Bool))).trans
      (Equiv.arrowCongr finTwoEquiv (Equiv.refl _))
  let eR : (Fin ((S * 4) * (2 * n)) → Bool) ≃ (Fin S → Fin 4 → Fin (2 * n) → Bool) :=
    (FunFamily.blocks (S * 4) (2 * n)).trans (blocksEquivX S 4 (Fin (2 * n) → Bool))
  (splitTape S n).trans (eK.prodCongr (eR.prodCongr (FunFamily.blocks S 2)))

/-- Key bit `t` of choice `b` at vertex `v` is tape bit `(b*S+v)*n+t`:
`(blocksEquiv S n r).1 b v t = (ofFn r).getD ((b.toNat*S+v)*n+t) false`.
The equation includes zero-width key tables. -/
theorem blocksEquiv_key (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool)
    (b : Bool) (v : Fin S) (t : Fin n) :
    (blocksEquiv S n r).1 b v t =
      (List.ofFn r).getD ((b.toNat * S + v) * n + t) false := by
  change blocksEquivX 2 S (Fin n → Bool)
    (FunFamily.blocks (2 * S) n ((splitTape S n r).1)) (finTwoEquiv.symm b) v t = _
  rw [blocksEquivX_apply, FunFamily.blocks_apply, splitTape_key]
  congr 1
  simp only [finProdFinEquiv_apply_val]
  have hb : (finTwoEquiv.symm b : ℕ) = b.toNat := by cases b <;> rfl
  rw [hb]
  ring

/-- Row-coin bit `t` of assignment index `a` at gate `i` is tape bit
`2 S n + (4 i + a) (2 n) + t`, for every `S` and `n`. -/
theorem blocksEquiv_row (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool)
    (i : Fin S) (a : Fin 4) (t : Fin (2 * n)) :
    (blocksEquiv S n r).2.1 i a t =
      (List.ofFn r).getD (2 * S * n + (4 * i + a) * (2 * n) + t) false := by
  change blocksEquivX S 4 (Fin (2 * n) → Bool)
    (FunFamily.blocks (S * 4) (2 * n) ((splitTape S n r).2.1)) i a t = _
  rw [blocksEquivX_apply, FunFamily.blocks_apply, splitTape_row]
  congr 1
  simp only [finProdFinEquiv_apply_val]
  ring

/-- Shift bit `t` at gate `i` is tape bit `10 S n + 2 i + t`, including `n = 0`. -/
theorem blocksEquiv_shift (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool)
    (i : Fin S) (t : Fin 2) :
    (blocksEquiv S n r).2.2 i t =
      (List.ofFn r).getD (10 * S * n + 2 * i + t) false := by
  change FunFamily.blocks S 2 ((splitTape S n r).2.2) i t = _
  rw [FunFamily.blocks_apply, splitTape_shift]
  congr 1
  rw [finProdFinEquiv_apply_val]
  ring

/-- `blocksEquiv S n r` is exactly the key, row and shift tables at their
specified tape offsets. -/
theorem blocksEquiv_eq (S n : ℕ) (r : Fin (10 * S * n + 2 * S) → Bool) :
    blocksEquiv S n r =
      ((fun (b : Bool) (v : Fin S) (t : Fin n) =>
          (List.ofFn r).getD ((b.toNat * S + v) * n + t) false),
        (fun (i : Fin S) (a : Fin 4) (t : Fin (2 * n)) =>
          (List.ofFn r).getD (2 * S * n + (4 * i + a) * (2 * n) + t) false),
        (fun (i : Fin S) (t : Fin 2) =>
          (List.ofFn r).getD (10 * S * n + 2 * i + t) false)) := by
  apply Prod.ext
  · funext b v t
    exact blocksEquiv_key S n r b v t
  · apply Prod.ext
    · funext i a t
      exact blocksEquiv_row S n r i a t
    · funext i t
      exact blocksEquiv_shift S n r i t

/-- Relabel a key table by changing choice `b` at `v` to `b XOR values v`.
This is an involutive permutation of complete key tables. -/
def keyRelabel (S n : ℕ) (values : Fin S → Bool) :
    Equiv.Perm (Bool → Fin S → Fin n → Bool) :=
  Function.Involutive.toPerm
    (fun k b v t => k (xor b (values v)) v t) fun k => by
      funext b v t
      simp only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- `keyRelabel S n values k b v t = k (b XOR values v) v t`. -/
theorem keyRelabel_eq (S n : ℕ) (values : Fin S → Bool)
    (k : Bool → Fin S → Fin n → Bool) (b : Bool) (v : Fin S) (t : Fin n) :
    keyRelabel S n values k b v t = k (xor b (values v)) v t := rfl

/-- Relabel row tables by the supplied assignment-index permutation at each gate:
`rowRelabel S n rows k i a t = k i (rows i a) t`. -/
def rowRelabel (S n : ℕ) (rows : Fin S → Equiv.Perm (Fin 4)) :
    Equiv.Perm (Fin S → Fin 4 → Fin (2 * n) → Bool) :=
  Equiv.piCongrRight fun i => Equiv.arrowCongr (rows i).symm (Equiv.refl _)

/-- `rowRelabel S n rows k i a t = k i (rows i a) t`. -/
theorem rowRelabel_eq (S n : ℕ) (rows : Fin S → Equiv.Perm (Fin 4))
    (k : Fin S → Fin 4 → Fin (2 * n) → Bool) (i : Fin S) (a : Fin 4)
    (t : Fin (2 * n)) : rowRelabel S n rows k i a t = k i (rows i a) t := rfl

/-- XOR each two-bit shift with its supplied mask, reusing the public `xorPerm`:
`shiftRelabel S mask k i t = k i t XOR mask i t`. -/
def shiftRelabel (S : ℕ) (mask : Fin S → Fin 2 → Bool) :
    Equiv.Perm (Fin S → Fin 2 → Bool) :=
  Equiv.piCongrRight fun i => xorPerm (mask i)

/-- `shiftRelabel S mask k i t = k i t XOR mask i t`. -/
theorem shiftRelabel_eq (S : ℕ) (mask : Fin S → Fin 2 → Bool)
    (k : Fin S → Fin 2 → Bool) (i : Fin S) (t : Fin 2) :
    shiftRelabel S mask k i t = xor (k i t) (mask i t) := by
  change xorPerm (mask i) (k i) t = _
  exact congrFun (xorPerm_apply (mask i) (k i)) t

/-- Relabel the key, row and shift tables independently by their supplied choice
flips, row permutations and shift masks. [PS10, Theorem 163.7] -/
def blockRelabel (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool) :
    Equiv.Perm (Blocks S n) :=
  (keyRelabel S n values).prodCongr ((rowRelabel S n rows).prodCongr (shiftRelabel S mask))

/-- `blockRelabel` applies `keyRelabel`, `rowRelabel` and `shiftRelabel` to the
three components of the block triple. -/
theorem blockRelabel_eq (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool) (q : Blocks S n) :
    blockRelabel S n values rows mask q =
      (keyRelabel S n values q.1, rowRelabel S n rows q.2.1, shiftRelabel S mask q.2.2) := rfl

/-- Conjugating `blockRelabel` by `blocksEquiv` gives a permutation of all
`10 S n + 2 S` tape bits. [PS10, Theorem 163.7; BMR90] -/
def relabel (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool) :
    Equiv.Perm (Fin (10 * S * n + 2 * S) → Bool) :=
  (blocksEquiv S n).trans ((blockRelabel S n values rows mask).trans (blocksEquiv S n).symm)

/-- `relabel S n values rows mask r` is the inverse block encoding of the
relabeled block triple of `r`. -/
theorem relabel_eq (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) :
    relabel S n values rows mask r =
      (blocksEquiv S n).symm (blockRelabel S n values rows mask (blocksEquiv S n r)) := rfl

/-- Encoding `relabel r` as blocks gives exactly `blockRelabel (blocksEquiv r)`:
`blocksEquiv S n (relabel S n values rows mask r) =
 blockRelabel S n values rows mask (blocksEquiv S n r)`. -/
theorem relabel_blocks (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) :
    blocksEquiv S n (relabel S n values rows mask r) =
      blockRelabel S n values rows mask (blocksEquiv S n r) := by
  rw [relabel_eq, Equiv.apply_symm_apply]

/-- In the relabeled tape, key choice `b` at `v` reads the original key choice
`b XOR values v` at that same vertex. -/
theorem relabel_key (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) (b : Bool) (v : Fin S) (t : Fin n) :
    (blocksEquiv S n (relabel S n values rows mask r)).1 b v t =
      (blocksEquiv S n r).1 (xor b (values v)) v t := by
  simp only [relabel_blocks, blockRelabel_eq, keyRelabel_eq]

/-- Row `a` of gate `i` in the relabeled tape reads original row `rows i a`,
with the within-row nonce coordinate unchanged. -/
theorem relabel_row (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (a : Fin 4) (t : Fin (2 * n)) :
    (blocksEquiv S n (relabel S n values rows mask r)).2.1 i a t =
      (blocksEquiv S n r).2.1 i (rows i a) t := by
  simp only [relabel_blocks, blockRelabel_eq, rowRelabel_eq]

/-- Shift bit `t` at gate `i` in the relabeled tape is the original shift bit
XOR the supplied mask bit `mask i t`. -/
theorem relabel_shift (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (t : Fin 2) :
    (blocksEquiv S n (relabel S n values rows mask r)).2.2 i t =
      xor ((blocksEquiv S n r).2.2 i t) (mask i t) := by
  simp only [relabel_blocks, blockRelabel_eq, shiftRelabel_eq]

/-- At exact tape offsets, relabeling replaces key choice `b` by
`b XOR values v`: the coordinate `(b*S+v)*n+t` reads `((b XOR values v)*S+v)*n+t`. -/
theorem relabel_key_getD (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) (b : Bool) (v : Fin S) (t : Fin n) :
    (List.ofFn (relabel S n values rows mask r)).getD ((b.toNat * S + v) * n + t) false =
      (List.ofFn r).getD (((xor b (values v)).toNat * S + v) * n + t) false := by
  rw [← blocksEquiv_key S n (relabel S n values rows mask r) b v t,
    relabel_key, blocksEquiv_key]

/-- At exact row-coin offsets, relabeling replaces assignment code `a` by
`rows i a` and keeps nonce bit `t` unchanged. -/
theorem relabel_row_getD (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (a : Fin 4) (t : Fin (2 * n)) :
    (List.ofFn (relabel S n values rows mask r)).getD
        (2 * S * n + (4 * i + a) * (2 * n) + t) false =
      (List.ofFn r).getD (2 * S * n + (4 * i + (rows i a : ℕ)) * (2 * n) + t) false := by
  rw [← blocksEquiv_row S n (relabel S n values rows mask r) i a t,
    relabel_row, blocksEquiv_row]

/-- At tape offset `10 S n + 2 i + t`, relabeling XORs the existing shift bit
with `mask i t`, including when the key length is zero. -/
theorem relabel_shift_getD (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (t : Fin 2) :
    (List.ofFn (relabel S n values rows mask r)).getD (10 * S * n + 2 * i + t) false =
      xor ((List.ofFn r).getD (10 * S * n + 2 * i + t) false) (mask i t) := by
  rw [← blocksEquiv_shift S n (relabel S n values rows mask r) i t,
    relabel_shift, blocksEquiv_shift]

/-- A key block at a vertex whose value mask is `false` is unchanged by relabeling.
This preserves unused key blocks when their value masks are set to `false`. -/
theorem relabel_key_fixed (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) (b : Bool) (v : Fin S) (t : Fin n)
    (hv : values v = false) :
    (List.ofFn (relabel S n values rows mask r)).getD ((b.toNat * S + v) * n + t) false =
      (List.ofFn r).getD ((b.toNat * S + v) * n + t) false := by
  rw [relabel_key_getD, hv, Bool.xor_false]

/-- A row coordinate fixed by `rows i` keeps every nonce bit. In particular,
callers preserve unused assignment codes by fixing them in the supplied permutation. -/
theorem relabel_row_fixed (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (a : Fin 4) (t : Fin (2 * n))
    (ha : rows i a = a) :
    (List.ofFn (relabel S n values rows mask r)).getD
        (2 * S * n + (4 * i + a) * (2 * n) + t) false =
      (List.ofFn r).getD (2 * S * n + (4 * i + a) * (2 * n) + t) false := by
  rw [relabel_row_getD, ha]

/-- A shift bit with a `false` mask is unchanged. Callers can therefore preserve
unused shift positions by setting exactly those mask bits to `false`. -/
theorem relabel_shift_fixed (S n : ℕ) (values : Fin S → Bool)
    (rows : Fin S → Equiv.Perm (Fin 4)) (mask : Fin S → Fin 2 → Bool)
    (r : Fin (10 * S * n + 2 * S) → Bool) (i : Fin S) (t : Fin 2)
    (ht : mask i t = false) :
    (List.ofFn (relabel S n values rows mask r)).getD (10 * S * n + 2 * i + t) false =
      (List.ofFn r).getD (10 * S * n + 2 * i + t) false := by
  rw [relabel_shift_getD, ht, Bool.xor_false]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel
