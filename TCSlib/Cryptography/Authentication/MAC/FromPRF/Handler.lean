/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Forwarding
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Generic
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The handler of the PRF-MAC reduction

The distinguisher of [PS10, Theorem 135.4] runs a MAC forger against its own function oracle: it
answers each tagging query `m` with the oracle's value at `m`, and at the end it asks the oracle at
the forger's output message `m*` and accepts iff the answer is the output tag `σ*` and `m*` was
never queried. This file builds it as a `Games.InteractiveHandler` (`macHandler q ℓ t`) with one
inner and one outer oracle, both with `ℓ(n)`-bit queries and `t(n)`-bit answers.

* **The state** keeps the queried messages, newest first, as blocks `1 ‖ m` of `ℓ(n) + 1` bits,
  followed by zeros, in `q(n) · (ℓ(n) + 1)` bits (`macState`). A query shifts its block in and
  drops the last `ℓ(n) + 1` bits, which are zeros while at most `q(n)` messages are stored.
* **One call** forwards the query and stores it (`macHandler_impl`).
* **The finalization** asks the outer oracle at the first `ℓ(n)` bits `m*` of the forger's output
  and returns the bit `[y = σ*] ∧ [m* fresh]`, where `σ*` is the rest of the output and `y` the
  answer; freshness is read from the state block by block with the chunk map `NMSim.chunkMap`
  (`macHandler_finish`).

## Main definitions

* `PRFMAC.blockLen`, `PRFMAC.macStLen`: the block and state lengths.
* `PRFMAC.blocks`, `PRFMAC.macState`: the encoded state of a list of queried messages.
* `PRFMAC.macHandler q ℓ t`: the handler.

## Main results

* `PRFMAC.finish_of_query_padFin`: a finalization with one outer query (generic).
* `PRFMAC.macHandler_impl`, `PRFMAC.macHandler_finish`: the handler's call and finalization on
  encoded states; `PRFMAC.macHandler_init_eq`: the initial state.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 135.4 (book p. 135).
-/

namespace TCSlib.Cryptography.Authentication.PRFMAC

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Games.InteractiveHandler (rU rS rI rX rL rAns finA)
open TCSlib.Cryptography.Composability.NMSim (chunkMap chunkMap_flatten polyTimeComputable_chunkMap)

/-! ### A finalization with one outer query -/

section FinishQuery

variable {k k' : ℕ} {din dout : Fin k → PolyExpr} {din' dout' : Fin k' → PolyExpr}

/-- **A finalization with one outer query, on lists:** if the finalization's first round asks
the outer query `x'` to oracle `j`, and its second round, with the answer `y` in the outer log,
returns `⟨[true], b y⟩` with `|b y| = outLen(n)`, then (with `finCall(n) ≥ 1`)
`H.finish n z ω s a = query j x' (fun y => pure (padFin _ (b y)))`.

**Proof sketch.** As `InteractiveHandler.impl_of_query`: unfold the finalization (`finish_eq`) at
the budget `finCall = p + 1`; the first round decodes to the query (`decodeBitMove_query`), which
`buildComp_succ_of_query` asks; after the answer `y` the log encodes as in `hrun₁`
(`bitCodec_encodeEntry`), and the second round decodes to the output `padFin _ (b y)`
(`ofFn_padFin_of_length`, `decodeBitMove_ret`, `buildComp_of_ret`). -/
theorem finish_of_query_padFin (H : InteractiveHandler k din dout k' din' dout') (n : ℕ)
    (z : List Bool) (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool)
    {d : ℕ} (a : Fin d → Bool) (j : Fin k') (x' : Fin ((din' j).eval n) → Bool)
    (b : (Fin ((dout' j).eval n) → Bool) → List Bool) (hb : ∀ y, (b y).length = H.outLen.eval n)
    (hfc : 1 ≤ H.finCall.eval n)
    (hrun₀ : H.finRun (InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
      []) = pairEncode [false] (pairEncode (List.replicate j true) (List.ofFn x')))
    (hrun₁ : ∀ y, H.finRun (InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s)
      (List.ofFn a) (pairEncode (pairEncode (List.replicate j true)
        (pairEncode (List.ofFn x') (List.ofFn y))) [])) = pairEncode [true] (b y)) :
    H.finish n z ω s a = .query j x' fun y => .pure (padFin _ (b y)) := by
  obtain ⟨p, hp⟩ : ∃ p, H.finCall.eval n = p + 1 := ⟨H.finCall.eval n - 1, by omega⟩
  rw [InteractiveHandler.finish_eq, hp,
    buildComp_succ_of_query (i := j) (x := x') (by
      rw [MachineCodec.encodeLog_nil, hrun₀]
      exact decodeBitMove_query (fun j => (din' j).eval n) (fun j => (dout' j).eval n) _ j x')]
  congr 1
  funext y
  have hlog : (bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog
      ([] ++ [⟨j, x', y⟩]) = pairEncode (pairEncode (List.replicate j true)
        (pairEncode (List.ofFn x') (List.ofFn y))) [] := by
    rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
      bitCodec_encodeEntry]
  refine buildComp_of_ret ?_
  have h := decodeBitMove_ret (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
    (H.outLen.eval n) (padFin _ (b y))
  rwa [ofFn_padFin_of_length (hb y), ← hrun₁, ← hlog] at h

end FinishQuery

/-! ### Lengths and the encoded state -/

/-- The length of a state block, a marker bit and a message: `blockLen ℓ = ℓ + 1`. -/
def blockLen (ℓ : PolyExpr) : PolyExpr := .add ℓ (.const 1)

/-- `(blockLen ℓ).eval n = ℓ(n) + 1`. -/
theorem blockLen_eval (ℓ : PolyExpr) (n : ℕ) : (blockLen ℓ).eval n = ℓ.eval n + 1 := by
  rw [blockLen, PolyExpr.eval_add, PolyExpr.eval_const]

/-- The state length, `q` blocks: `macStLen q ℓ = q · (ℓ + 1)`. -/
def macStLen (q ℓ : PolyExpr) : PolyExpr := .mul q (blockLen ℓ)

/-- `(macStLen q ℓ).eval n = q(n) · (ℓ(n) + 1)`. -/
theorem macStLen_eval (q ℓ : PolyExpr) (n : ℕ) :
    (macStLen q ℓ).eval n = q.eval n * (ℓ.eval n + 1) := by
  rw [macStLen, PolyExpr.eval_mul, blockLen_eval]

/-- The blocks of a list of messages, each message `m` as `1 ‖ m`:
`blocks L = (L.map fun m => true :: ⟦m⟧).flatten`. -/
def blocks {a : ℕ} (L : List (Fin a → Bool)) : List Bool :=
  (L.map fun m => true :: List.ofFn m).flatten

/-- `blocks L = (L.map fun m => true :: ⟦m⟧).flatten`. -/
theorem blocks_eq {a : ℕ} (L : List (Fin a → Bool)) :
    blocks L = (L.map fun m => true :: List.ofFn m).flatten :=
  rfl

/-- `blocks (m :: L) = true :: ⟦m⟧ ++ blocks L`. -/
theorem blocks_cons {a : ℕ} (m : Fin a → Bool) (L : List (Fin a → Bool)) :
    blocks (m :: L) = true :: List.ofFn m ++ blocks L := by
  rw [blocks_eq, blocks_eq, List.map_cons, List.flatten_cons]

/-- Each block has `a + 1` bits: `|blocks L| = |L| · (a + 1)`. -/
theorem length_blocks {a : ℕ} (L : List (Fin a → Bool)) :
    (blocks L).length = L.length * (a + 1) := by
  induction L with
  | nil => rw [blocks_eq, List.map_nil, List.flatten_nil, List.length_nil, List.length_nil,
      Nat.zero_mul]
  | cons m L ih =>
    rw [blocks_cons, List.length_append, List.length_cons, List.length_ofFn, ih,
      List.length_cons]
    ring

/-! ### The round and the finalization -/

/-- One round of a call: with an empty outer log, ask the outer oracle the query; with the answer
`y` in the log, return `y` and the state with the block `1 ‖ x` shifted in and cut to `q(n)` blocks.
-/
private def macRun (q ℓ : PolyExpr) (w : List Bool) : List Bool :=
  if decide (rL w = []) then pairEncode [false] (pairEncode (rI w) (rX w))
  else pairEncode [true]
    (rAns w ++ ([true] ++ rX w ++ rS w).take ((macStLen q ℓ).eval (rU w).length))

/-- The round is polynomial-time. -/
private theorem polyTimeComputable_macRun (q ℓ : PolyExpr) : PolyTimeComputable (macRun q ℓ) := by
  have hcut : PolyTimeComputable fun w : List Bool =>
      ([true] ++ rX w ++ rS w).take ((macStLen q ℓ).eval (rU w).length) :=
    ((polyTimeComputable_pairTakePoly (macStLen q ℓ)).comp
      (InteractiveHandler.polyTimeComputable_rU.pairEncode
        (((polyTimeComputable_const [true]).append InteractiveHandler.polyTimeComputable_rX).append
          InteractiveHandler.polyTimeComputable_rS))).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact polyTimeComputable_ite
    (polyTimeComputable_isNil.comp InteractiveHandler.polyTimeComputable_rL)
    ((polyTimeComputable_const [false]).pairEncode
      (InteractiveHandler.polyTimeComputable_rI.pairEncode
        InteractiveHandler.polyTimeComputable_rX))
    ((polyTimeComputable_const [true]).pairEncode
      (InteractiveHandler.polyTimeComputable_rAns.append hcut))

/-- The output message of a finalization input: the first `ℓ(n)` bits of the forger's output. -/
private def msgOf (ℓ : PolyExpr) (w : List Bool) : List Bool :=
  (finA w).take (ℓ.eval (rU w).length)

/-- The output tag of a finalization input: the forger's output after its first `ℓ(n)` bits. -/
private def sigOf (ℓ : PolyExpr) (w : List Bool) : List Bool :=
  (finA w).drop (ℓ.eval (rU w).length)

/-- The emission of the freshness test on a block: `[true]` iff the block is `1 ‖ m*`, where `m*`
is the second component of the context. -/
private def hitEmit (ctx ch : List Bool) : List Bool :=
  if decide (ch = [true] ++ pairSndD ctx) then [true] else []

/-- The blocks of the state equal to `1 ‖ m*`, one `true` each (a chunk map over the state). -/
private def hitsOf (ℓ : PolyExpr) (w : List Bool) : List Bool :=
  chunkMap (blockLen ℓ) hitEmit (pairEncode (pairEncode (rU w) (msgOf ℓ w)) (rS w))

/-- One round of the finalization: with an empty outer log, ask the oracle at `m*`; with the
answer `y` in the log, return the bit `[y = σ*] ∧ [no block is 1 ‖ m*]`. -/
private def macFin (ℓ : PolyExpr) (w : List Bool) : List Bool :=
  if decide (rL w = []) then pairEncode [false] (pairEncode [] (msgOf ℓ w))
  else pairEncode [true]
    (if decide (rAns w = sigOf ℓ w) then [decide (hitsOf ℓ w = [])] else [false])

/-- The finalization round is polynomial-time.

**Proof sketch.** Its pieces are built from the published readers (`rU`, `rL`, `rS`, `rAns`,
`finA`) with the pair primitives: the message and tag by `polyTimeComputable_pairTakePoly` and
`polyTimeComputable_pairDropPoly`, the block test by `polyTimeComputable_pairEq`, the freshness
test by the chunk map (`NMSim.polyTimeComputable_chunkMap`) and `polyTimeComputable_isNil`, and
the branches by `polyTimeComputable_ite`. -/
private theorem polyTimeComputable_macFin (ℓ : PolyExpr) : PolyTimeComputable (macFin ℓ) := by
  have hU := InteractiveHandler.polyTimeComputable_rU
  have hA := InteractiveHandler.polyTimeComputable_finA
  have hmsg : PolyTimeComputable (msgOf ℓ) :=
    ((polyTimeComputable_pairTakePoly ℓ).comp (hU.pairEncode hA)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, msgOf]
  have hsig : PolyTimeComputable (sigOf ℓ) :=
    ((polyTimeComputable_pairDropPoly ℓ).comp (hU.pairEncode hA)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, sigOf]
  have hemit : PolyTimeComputable fun z => hitEmit (pairFstD z) (pairSndD z) := by
    have hc : PolyTimeComputable fun z : List Bool =>
        [decide (pairSndD z = [true] ++ pairSndD (pairFstD z))] :=
      (polyTimeComputable_pairEq.comp (polyTimeComputable_pairSndD.pairEncode
        ((polyTimeComputable_const [true]).append
          (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)))).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
    exact (polyTimeComputable_ite hc (polyTimeComputable_const [true])
      (polyTimeComputable_const [])).congr fun z => by simp only [hitEmit]
  have hhits : PolyTimeComputable (hitsOf ℓ) :=
    ((polyTimeComputable_chunkMap (blockLen ℓ) hemit).comp
      ((hU.pairEncode hmsg).pairEncode InteractiveHandler.polyTimeComputable_rS)).congr fun w => by
      simp only [Function.comp_apply, hitsOf]
  have hbit : PolyTimeComputable fun w : List Bool =>
      if decide (rAns w = sigOf ℓ w) then [decide (hitsOf ℓ w = [])] else [false] :=
    polyTimeComputable_ite
      ((polyTimeComputable_pairEq.comp
        (InteractiveHandler.polyTimeComputable_rAns.pairEncode hsig)).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])
      (polyTimeComputable_isNil.comp hhits) (polyTimeComputable_const [false])
  exact polyTimeComputable_ite
    (polyTimeComputable_isNil.comp InteractiveHandler.polyTimeComputable_rL)
    ((polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_const []).pairEncode hmsg))
    ((polyTimeComputable_const [true]).pairEncode hbit)

/-! ### The handler -/

/-- **The handler of the PRF-MAC reduction** [PS10, Theorem 135.4, proof], for the query budget
`q` and `ℓ(n)`-bit messages with `t(n)`-bit tags: one inner and one outer oracle, both with these
lengths; the state keeps the queried messages in `q(n) · (ℓ(n) + 1)` bits; no seed; one outer
query per call, which forwards the inner query; the adversary gets the empty input; the
finalization makes one outer query and returns one bit:
`(macHandler q ℓ t).stateLen = macStLen q ℓ`, `seedLen = .const 0`,
`perCall = finCall = outLen = .const 1` and `advIn _ = []` (the `simps` fields). -/
def macHandler (q ℓ t : PolyExpr) :
    InteractiveHandler 1 (fun _ => ℓ) (fun _ => t) 1 (fun _ => ℓ) (fun _ => t) where
  stateLen := macStLen q ℓ
  seedLen := .const 0
  perCall := .const 1
  init _ := zeroBits _
  run := macRun q ℓ
  poly := polyTimeComputable_macRun q ℓ
  advIn _ := []
  advIn_poly := polyTimeComputable_const []
  outLen := .const 1
  finCall := .const 1
  finRun := macFin ℓ
  finRun_poly := polyTimeComputable_macFin ℓ

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall init advIn outLen finCall]
  macHandler

variable (q ℓ t : PolyExpr)

/-- **The encoded state** of the queried messages `L` (newest first): their blocks `1 ‖ m`,
followed by zeros, read at the state length: `macState q ℓ t n L = padFin _ (blocks L)`. -/
def macState (n : ℕ) (L : List (Fin (ℓ.eval n) → Bool)) :
    Fin ((macHandler q ℓ t).stateLen.eval n) → Bool :=
  padFin _ (blocks L)

/-- `macState q ℓ t n L = padFin _ (blocks L)`. -/
theorem macState_eq (n : ℕ) (L : List (Fin (ℓ.eval n) → Bool)) :
    macState q ℓ t n L = padFin _ (blocks L) :=
  rfl

/-- The state has `q(n) · (ℓ(n) + 1)` bits:
`(macHandler q ℓ t).stateLen.eval n = q(n) · (ℓ(n) + 1)`. -/
theorem macHandler_stateLen_eval (n : ℕ) :
    (macHandler q ℓ t).stateLen.eval n = q.eval n * (ℓ.eval n + 1) := by
  rw [macHandler_stateLen, macStLen_eval]

/-- **The initial state stores no message:** `(macHandler q ℓ t).init n = macState q ℓ t n []`. -/
theorem macHandler_init_eq (n : ℕ) : (macHandler q ℓ t).init n = macState q ℓ t n [] := by
  funext j
  rw [macHandler_init, macState_eq, zeroBits_apply, padFin_def, blocks_eq, List.map_nil,
    List.flatten_nil]
  rfl

/-- The encoded state of at most `q(n)` messages is their blocks followed by zeros:
`⟦macState q ℓ t n L⟧ = blocks L ++ 0^{q(n)(ℓ(n)+1) − |L|(ℓ(n)+1)}`. -/
theorem ofFn_macState (n : ℕ) (L : List (Fin (ℓ.eval n) → Bool)) (hL : L.length ≤ q.eval n) :
    List.ofFn (macState q ℓ t n L) = blocks L ++
      List.replicate (q.eval n * (ℓ.eval n + 1) - L.length * (ℓ.eval n + 1)) false := by
  rw [macState_eq, Collection.ofFn_padFin_of_le, length_blocks, macHandler_stateLen_eval]
  rw [macHandler_stateLen_eval, length_blocks]
  exact Nat.mul_le_mul_right _ hL

/-! ### The call -/

/-- **One call forwards the query and stores it:** from the encoded state of `L` with
`|L| < q(n)`, the inner query `x` is the outer query `x`, answered with the outer answer `y` and
the state of `x :: L`: `(macHandler q ℓ t).impl n z ω i x (macState q ℓ t n L) =
query i x (fun y => pure (y, macState q ℓ t n (x :: L)))`.

**Proof sketch.** `InteractiveHandler.impl_of_query_padFin` with one outer query: the first round
has an empty outer log (`rL_input`) and asks `⟨1^i, x⟩` (`rI_input`, `rX_input`); the second reads
the answer (`rAns_input`) and returns it with `(1 ‖ x ‖ ⟦s⟧)` cut to `q(n)(ℓ(n) + 1)` bits. With
`⟦s⟧ = blocks L ‖ 0…0` (`ofFn_macState`) the cut drops `ℓ(n) + 1` zeros (`List.take_append`,
`List.take_replicate`) and leaves the encoded state of `x :: L`. -/
theorem macHandler_impl (n : ℕ) (z : List Bool) (ω : Fin ((macHandler q ℓ t).seedLen.eval n) → Bool)
    (i : Fin 1) (x : Fin (ℓ.eval n) → Bool) (L : List (Fin (ℓ.eval n) → Bool))
    (hL : L.length < q.eval n) :
    (macHandler q ℓ t).impl n z ω i x (macState q ℓ t n L) =
      .query i x fun y => .pure (y, macState q ℓ t n (x :: L)) := by
  have hN := macHandler_stateLen_eval q ℓ t n
  have hcut : ([true] ++ List.ofFn x ++ List.ofFn (macState q ℓ t n L)).take
      ((macStLen q ℓ).eval (List.replicate n true).length) =
      List.ofFn (macState q ℓ t n (x :: L)) := by
    have hle : (L.length + 1) * (ℓ.eval n + 1) ≤ q.eval n * (ℓ.eval n + 1) :=
      Nat.mul_le_mul_right _ hL
    rw [List.length_replicate, macStLen_eval, ofFn_macState q ℓ t n L hL.le,
      ofFn_macState q ℓ t n (x :: L) hL, blocks_cons, List.length_cons]
    have hB : ([true] ++ List.ofFn x ++ blocks L).length = (L.length + 1) * (ℓ.eval n + 1) := by
      rw [List.length_append, List.length_append, List.length_ofFn, length_blocks]
      simp only [List.length_singleton]
      ring
    rw [← List.append_assoc, List.take_append, List.take_of_length_le (by rw [hB]; exact hle), hB,
      List.take_replicate]
    have hmin : min (q.eval n * (ℓ.eval n + 1) - (L.length + 1) * (ℓ.eval n + 1))
        (q.eval n * (ℓ.eval n + 1) - L.length * (ℓ.eval n + 1)) =
        q.eval n * (ℓ.eval n + 1) - (L.length + 1) * (ℓ.eval n + 1) :=
      Nat.min_eq_left (Nat.sub_le_sub_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _)
    rw [hmin]
    simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine (InteractiveHandler.impl_of_query_padFin _ n z ω i x (macState q ℓ t n L) i x
    (fun y => List.ofFn y) (fun _ => List.ofFn (macState q ℓ t n (x :: L)))
    (fun y => List.length_ofFn) (fun _ => List.length_ofFn)
    (by rw [macHandler_perCall, PolyExpr.eval_const]) ?_ fun y => ?_).trans ?_
  · show macRun q ℓ _ = _
    rw [macRun, InteractiveHandler.rL_input, InteractiveHandler.rI_input,
      InteractiveHandler.rX_input, if_pos (decide_eq_true rfl)]
  · show macRun q ℓ _ = _
    rw [macRun, InteractiveHandler.rL_input, InteractiveHandler.rAns_input,
      InteractiveHandler.rX_input, InteractiveHandler.rS_input, InteractiveHandler.rU_input,
      if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h)), hcut]
  · simp only [padFin_ofFn]

/-! ### The finalization -/

/-- The freshness test on the encoded state of at most `q(n)` messages: no block is `1 ‖ u` iff no
stored message has the list `u`: `chunkMap … ⟨⟨1^n, u⟩, ⟦macState q ℓ t n L⟧⟩ = [] ↔
∀ m ∈ L, ⟦m⟧ ≠ u`.

**Proof sketch.** The state is the concatenation of the blocks `1 ‖ m` and of `q(n) − |L|` zero
blocks, all of `ℓ(n) + 1 > 0` bits (`ofFn_macState`, `List.flatten_replicate_replicate`), so the
chunk map emits `hitEmit` of each block (`NMSim.chunkMap_flatten`), and the result is empty iff
every emission is (`List.flatten_eq_nil_iff`). A block `1 ‖ m` emits iff `⟦m⟧ = u`
(`List.cons_injective`); a zero block starts with `0` and never emits. -/
private theorem hits_nil_iff (n : ℕ) (L : List (Fin (ℓ.eval n) → Bool))
    (hL : L.length ≤ q.eval n) (u : List Bool) :
    chunkMap (blockLen ℓ) hitEmit (pairEncode (pairEncode (List.replicate n true) u)
        (List.ofFn (macState q ℓ t n L))) = [] ↔ ∀ m ∈ L, List.ofFn m ≠ u := by
  have hflat : List.ofFn (macState q ℓ t n L) =
      (L.map (fun m => true :: List.ofFn m) ++
        List.replicate (q.eval n - L.length) (List.replicate (ℓ.eval n + 1) false)).flatten := by
    rw [ofFn_macState q ℓ t n L hL, List.flatten_append, List.flatten_replicate_replicate,
      blocks_eq, Nat.sub_mul]
  have hlen : ∀ ch ∈ L.map (fun m => true :: List.ofFn m) ++
      List.replicate (q.eval n - L.length) (List.replicate (ℓ.eval n + 1) false),
      ch.length = (blockLen ℓ).eval n := by
    intro ch hch
    rw [blockLen_eval]
    rcases List.mem_append.1 hch with h | h
    · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h
      rw [List.length_cons, List.length_ofFn]
    · rw [List.eq_of_mem_replicate h, List.length_replicate]
  rw [hflat, chunkMap_flatten (blockLen ℓ) hitEmit n u _ hlen
    (by rw [blockLen_eval]; omega), List.flatten_eq_nil_iff]
  constructor
  · intro h m hm hmu
    have := h _ (List.mem_map.2 ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨m, hm, rfl⟩), rfl⟩)
    rw [hitEmit, pairSndD_pairEncode, if_pos (decide_eq_true (by rw [hmu]; rfl))] at this
    exact List.cons_ne_nil _ _ this
  · intro h x hx
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hx
    rcases List.mem_append.1 hch with hc | hc
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hc
      rw [hitEmit, pairSndD_pairEncode, if_neg]
      intro he
      exact h m hm (List.cons_injective (of_decide_eq_true he))
    · rw [List.eq_of_mem_replicate hc, hitEmit, pairSndD_pairEncode, if_neg]
      intro he
      have := of_decide_eq_true he
      rw [List.replicate_succ] at this
      exact Bool.false_ne_true (List.cons_eq_cons.1 this).1

/-- **The finalization** from the encoded state of `L` with `|L| ≤ q(n)`, after the output `a`
of at least `ℓ(n)` bits: ask the oracle at `m* = a[0, ℓ(n))` and output the bit
`[⟦y⟧ = a[ℓ(n), …)] ∧ [∀ m ∈ L, ⟦m⟧ ≠ ⟦m*⟧]` for its answer `y`:
`(macHandler q ℓ t).finish n z ω (macState q ℓ t n L) a = query 0 (padFin _ (⟦a⟧.take ℓ(n)))
(fun y => pure (padFin _ [decide (⟦y⟧ = ⟦a⟧.drop ℓ(n)) && decide (∀ m ∈ L, ⟦m⟧ ≠ ⟦a⟧.take ℓ(n))]))`.

**Proof sketch.** `finish_of_query_padFin`. The first round has an empty outer log
(`rL_finInput`) and asks the first `ℓ(n)` bits of `a` (`finA_finInput`, `rU_finInput`). The second
reads the answer `y` from the one-entry log (`rAns_eq`, `rL_finInput`) and compares it with the rest
of `a`; the freshness test reads the state block by block (`NMSim.chunkMap_flatten` on the blocks
and the zero blocks, `ofFn_macState`): a zero block never starts with the marker bit. -/
theorem macHandler_finish (n : ℕ) (z : List Bool)
    (ω : Fin ((macHandler q ℓ t).seedLen.eval n) → Bool) (L : List (Fin (ℓ.eval n) → Bool))
    (hL : L.length ≤ q.eval n) {d : ℕ} (a : Fin d → Bool) (hd : ℓ.eval n ≤ d) :
    (macHandler q ℓ t).finish n z ω (macState q ℓ t n L) a =
      .query 0 (padFin _ ((List.ofFn a).take (ℓ.eval n))) fun y =>
        .pure (padFin _ [decide (List.ofFn y = (List.ofFn a).drop (ℓ.eval n)) &&
          decide (∀ m ∈ L, List.ofFn m ≠ (List.ofFn a).take (ℓ.eval n))]) := by
  have htake : ((List.ofFn a).take (ℓ.eval n)).length = ℓ.eval n := by
    rw [List.length_take, List.length_ofFn, Nat.min_eq_left hd]
  have hx : List.ofFn (padFin (ℓ.eval n) ((List.ofFn a).take (ℓ.eval n))) =
      (List.ofFn a).take (ℓ.eval n) := ofFn_padFin_of_length htake
  refine finish_of_query_padFin _ n z ω (macState q ℓ t n L) a 0
    (padFin _ ((List.ofFn a).take (ℓ.eval n))) _ (fun y => by
      rw [List.length_singleton, macHandler_outLen, PolyExpr.eval_const])
    (by rw [macHandler_finCall, PolyExpr.eval_const]) ?_ fun y => ?_
  · show macFin ℓ _ = _
    rw [macFin, InteractiveHandler.rL_finInput, if_pos (decide_eq_true rfl), msgOf,
      InteractiveHandler.finA_finInput, InteractiveHandler.rU_finInput, List.length_replicate, hx]
    rfl
  · show macFin ℓ _ = _
    have hans : rAns (InteractiveHandler.finInput n z (List.ofFn ω)
        (List.ofFn (macState q ℓ t n L)) (List.ofFn a)
        (pairEncode (pairEncode (List.replicate ((0 : Fin 1) : ℕ) true)
          (pairEncode (List.ofFn (padFin (ℓ.eval n) ((List.ofFn a).take (ℓ.eval n))))
            (List.ofFn y))) [])) = List.ofFn y := by
      rw [InteractiveHandler.rAns_eq, InteractiveHandler.rL_finInput, pairFstD_pairEncode,
        pairSndD_pairEncode, pairSndD_pairEncode]
    rw [macFin, InteractiveHandler.rL_finInput,
      if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h)), hans, sigOf, hitsOf, msgOf,
      InteractiveHandler.finA_finInput, InteractiveHandler.rU_finInput,
      InteractiveHandler.rS_finInput, List.length_replicate]
    congr 1
    by_cases hy : List.ofFn y = (List.ofFn a).drop (ℓ.eval n)
    · rw [if_pos (decide_eq_true hy), decide_eq_true hy, Bool.true_and]
      congr 1
      exact decide_eq_decide.2 (hits_nil_iff q ℓ t n L hL _)
    · rw [if_neg (fun h => hy (of_decide_eq_true h)), decide_eq_false hy, Bool.false_and]

end TCSlib.Cryptography.Authentication.PRFMAC
