/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency.Interactive
import TCSlib.Cryptography.Games.Efficiency.Handler
import TCSlib.Cryptography.Games.Efficiency.Replay

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The functional equation of the replay machine (efficiency fill, T2)

The replay machine of `TCSlib.Cryptography.Games.Efficiency.Interactive`, run as an oracle machine
against the outer oracles, **is** the reduction: its computation tree equals the simulation of the
adversary by the interactive handler followed by the finalization (`iRaw_spec`). Route note
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`, §"T2", steps 4 and 5.

The proof shows that the machine's next-move function replays the reduction tree
(`EffFill.ReplaysFrom`), by three nested inductions along the phases of the reduction, the
finalization (`fin_phase`), a call (`call_phase`) and the adversary (`adv_phase`). The invariant
(`IInv`) says that, on every outer log extending the replayed prefix, the activation loop has
reached the state word encoding the current position. The tree makes at most
`q(n) · perCall(n) + finCall(n)` queries (`costBoundedBy_mul`, `simulate_costBoundedBy`), so the
machine's budget never cuts the replay short (`buildComp_of_replaysFrom`).

## Main definitions

* `EffFill.iCall`, `EffFill.iImpl`, `EffFill.iFinish`: one call of the handler, the handler as an
  implementation, and the finalization, over the raw ingredients.
* `EffFill.iX`: the raw layout on the outer log `O`; `EffFill.IInv`: the replay invariant.

## Main results

* `EffFill.iRaw_spec`: the machine's computation is the reduction.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (closure of p.p.t. machines under efficient operations; for example the reductions of the
  proofs of Theorems 135.4 and 168.2).
-/

namespace TCSlib.Cryptography.Games.EffFill

open Complexity Turing

variable {k k' : ℕ}

/-- Cutting the string of a `(a + b)`-bit word at `a` gives its two parts:
`(ofFn w).take a = ofFn (w ∘ castAdd b)` and `(ofFn w).drop a = ofFn (w ∘ natAdd a)`. -/
theorem ofFn_take_drop_add {a b : ℕ} (w : Fin (a + b) → Bool) :
    (List.ofFn w).take a = List.ofFn (fun j => w (Fin.castAdd b j)) ∧
      (List.ofFn w).drop a = List.ofFn (fun j => w (Fin.natAdd a j)) := by
  rw [List.ofFn_add]
  exact ⟨List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn⟩

section Spec

variable (A : NUPPT) (q dα : PolyExpr) (din dout : Fin k → PolyExpr) (din' dout' : Fin k' →
    PolyExpr)
  (stateLen perCall outLen finCall : PolyExpr) (run advIn finRun : List Bool → List Bool)

/-- The next-move function of one call of the interactive handler on the inner query `x` to
oracle `i` in state `s`, at parameter `n` with the reduction's input `z` and seed `ω`: `run` on
`⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, decoded with result length `dout i + stateLen`. -/
def iCallNext (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool)
    (L : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))) :
    Move (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))
      (Fin ((dout i).eval n + stateLen.eval n) → Bool) :=
  decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
    ((dout i).eval n + stateLen.eval n)
    (run (pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
      (pairEncode (List.ofFn s) (pairEncode (pairEncode (List.replicate i true) (List.ofFn x))
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L)))))

/-- The defining equation of `iCallNext`. -/
theorem iCallNext_eq (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool)
    (L : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))) :
    iCallNext din dout din' dout' stateLen run n z ω s i x L =
      decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
        ((dout i).eval n + stateLen.eval n)
        (run (pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
          (pairEncode (List.ofFn s) (pairEncode (pairEncode (List.replicate i true) (List.ofFn x))
            ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))) :=
  rfl

/-- **One call** of the interactive handler: `buildComp` of `iCallNext` from the empty outer log
with budget `perCall(n)` and the joint all-`false` default (the term of
`InteractiveHandler.call`). -/
def iCall (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    OracleComp (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))
      (Fin ((dout i).eval n + stateLen.eval n) → Bool) :=
  buildComp (iCallNext din dout din' dout' stateLen run n z ω s i x) (zeroBits _) (perCall.eval n)
      []

/-- `iCall … = buildComp (iCallNext …) (zeroBits _) (perCall n) []`. -/
theorem iCall_eq_buildComp (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    iCall din dout din' dout' stateLen perCall run n z ω s i x =
      buildComp (iCallNext din dout din' dout' stateLen run n z ω s i x) (zeroBits _)
        (perCall.eval n) [] :=
  rfl

/-- The defining equation of `iCall`, with the next-move function written out. -/
theorem iCall_eq (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    iCall din dout din' dout' stateLen perCall run n z ω s i x =
      buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
          ((dout i).eval n + stateLen.eval n)
          (run (pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
            (pairEncode (List.ofFn s) (pairEncode (pairEncode (List.replicate i true) (List.ofFn x))
              ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))))
        (zeroBits _) (perCall.eval n) [] :=
  rfl

/-- **The handler as an implementation** of the inner oracles by the outer ones: one call per
inner query, its result split into the answer and the new state (the term of
`InteractiveHandler.impl`). -/
def iImpl (n : ℕ) (z ω : List Bool) :
    QueryImpl (bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n))
      (Fin (stateLen.eval n) → Bool) (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval
          n)) :=
  fun i x s => (iCall din dout din' dout' stateLen perCall run n z ω s i x).bind fun w =>
    .pure (fun j => w (Fin.castAdd (stateLen.eval n) j), fun j => w (Fin.natAdd ((dout i).eval n)
        j))

/-- The defining equation of `iImpl`. -/
theorem iImpl_apply (n : ℕ) (z ω : List Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (stateLen.eval n) → Bool) :
    iImpl din dout din' dout' stateLen perCall run n z ω i x s =
      (iCall din dout din' dout' stateLen perCall run n z ω s i x).bind fun w =>
        .pure (fun j => w (Fin.castAdd (stateLen.eval n) j), fun j => w (Fin.natAdd ((dout i).eval
            n) j)) :=
  rfl

/-- The next-move function of the finalization in state `s` after the adversary's output `a`:
`finRun` on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`, decoded with result length `outLen(n)`. -/
def iFinNext (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool)
    (L : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))) :
    Move (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))
      (Fin (outLen.eval n) → Bool) :=
  decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (outLen.eval n)
    (finRun (pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
      (pairEncode (List.ofFn s) (pairEncode (List.ofFn a)
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L)))))

/-- The defining equation of `iFinNext`. -/
theorem iFinNext_eq (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool)
    (L : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))) :
    iFinNext din' dout' stateLen outLen finRun n z ω s a L =
      decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (outLen.eval n)
        (finRun (pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
          (pairEncode (List.ofFn s) (pairEncode (List.ofFn a)
            ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))) :=
  rfl

/-- **The finalization** in state `s` after the adversary's output `a`: `buildComp` of
`iFinNext` with budget `finCall(n)` (the term of `InteractiveHandler.finish`). -/
def iFinish (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool)
    :
    OracleComp (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))
      (Fin (outLen.eval n) → Bool) :=
  buildComp (iFinNext din' dout' stateLen outLen finRun n z ω s a) (zeroBits _) (finCall.eval n) []

/-- `iFinish … = buildComp (iFinNext …) (zeroBits _) (finCall n) []`. -/
theorem iFinish_eq_buildComp (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) :
    iFinish din' dout' stateLen outLen finCall finRun n z ω s a =
      buildComp (iFinNext din' dout' stateLen outLen finRun n z ω s a) (zeroBits _)
        (finCall.eval n) [] :=
  rfl

/-- The defining equation of `iFinish`, with the next-move function written out. -/
theorem iFinish_eq (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) :
    iFinish din' dout' stateLen outLen finCall finRun n z ω s a =
      buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
          (outLen.eval n)
          (finRun (pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
            (pairEncode (List.ofFn s) (pairEncode (List.ofFn a)
              ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))))
        (zeroBits _) (finCall.eval n) [] :=
  rfl

/-- The raw layout of the machine on its outer log `O`:
`⟨⟨⟨1^n, ⟨⟨z, encodeLog O⟩, ω⟩⟩, ⟨A.advice n, s₀⟩⟩, r⟩`. -/
def iX (n : ℕ) (z ω : List Bool) (r : A.Coins n) (init : Fin (stateLen.eval n) → Bool)
    (O : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))) : List Bool :=
  NUPPT.layout (List.replicate n true)
    (pairEncode (pairEncode z
      ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (outLen.eval n)).encodeLog
          O))
      ω)
    (pairEncode (A.advice n) (List.ofFn init)) (List.ofFn r)

/-- The defining equation of `iX`. -/
theorem iX_eq (n : ℕ) (z ω : List Bool) (r : A.Coins n) (init : Fin (stateLen.eval n) → Bool)
    (O : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))) :
    iX A din' dout' stateLen outLen n z ω r init O =
      NUPPT.layout (List.replicate n true)
        (pairEncode (pairEncode z
          ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
            (outLen.eval n)).encodeLog O)) ω)
        (pairEncode (A.advice n) (List.ofFn init)) (List.ofFn r) :=
  rfl

/-- **The replay invariant:** on every outer log `P ++ O'` extending the replayed prefix `P`, the
activation loop has run `t` rounds without stopping, within the state bound, and reached the
state word `S O'`. -/
def IInv (n : ℕ) (z ω : List Bool) (r : A.Coins n) (init : Fin (stateLen.eval n) → Bool) (t : ℕ)
    (P : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n)))
    (S : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n)) → List Bool) :
    Prop :=
  ∀ O', RunsTo (iStart q) (iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun)
    (iBound q dα din dout din' stateLen perCall finCall dout')
    (iX A din' dout' stateLen outLen n z ω r init (P ++ O')) t (S O')

/-- `IInv … t P S ↔ ∀ O', RunsTo … (iX (P ++ O')) t (S O')`. -/
theorem iInv_iff (n : ℕ) (z ω : List Bool) (r : A.Coins n) (init : Fin (stateLen.eval n) → Bool)
    (t : ℕ) (P : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n)))
    (S : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n)) → List Bool) :
    IInv A q dα din dout din' dout' stateLen perCall outLen finCall run advIn finRun n z ω r init t
        P S ↔
      ∀ O', RunsTo (iStart q)
        (iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun)
        (iBound q dα din dout din' stateLen perCall finCall dout')
        (iX A din' dout' stateLen outLen n z ω r init (P ++ O')) t (S O') :=
  Iff.rfl

/-- The machine's next move on the outer log `O`: its output on the layout `iX O`, decoded with
the machine's codec. -/
def iNext (n : ℕ) (z ω : List Bool) (r : A.Coins n) (init : Fin (stateLen.eval n) → Bool)
    (O : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))) :
    Move (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))
      (Fin (outLen.eval n) → Bool) :=
  decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (outLen.eval n)
    (iRaw A q dα din dout din' stateLen perCall outLen finCall run advIn finRun dout'
      (iX A din' dout' stateLen outLen n z ω r init O))

/-- The defining equation of `iNext`. -/
theorem iNext_eq (n : ℕ) (z ω : List Bool) (r : A.Coins n) (init : Fin (stateLen.eval n) → Bool)
    (O : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))) :
    iNext A q dα din dout din' dout' stateLen perCall outLen finCall run advIn finRun n z ω r init O
        =
      decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (outLen.eval n)
        (iRaw A q dα din dout din' stateLen perCall outLen finCall run advIn finRun dout'
          (iX A din' dout' stateLen outLen n z ω r init O)) :=
  rfl

/-- **The rest of the reduction** from an adversary's position: the simulation, by the handler from
state `s`, of the adversary's computation from its log `hist` with remaining budget `b`, followed
by the finalization. -/
def iTree (n : ℕ) (z ω : List Bool) (r : A.Coins n)
    (hist : QueryLog (bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)))
    (s : Fin (stateLen.eval n) → Bool) (b : ℕ) :
    OracleComp (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))
      (Fin (outLen.eval n) → Bool) :=
  (simulate (iImpl din dout din' dout' stateLen perCall run n z ω)
    (buildComp (advNext A (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval
        n))
      n (advIn (pairEncode (List.replicate n true) (pairEncode z ω))) r) (zeroBits _) b hist)
          s).bind
    fun res => iFinish din' dout' stateLen outLen finCall finRun n z ω res.2 res.1

/-- The defining equation of `iTree`. -/
theorem iTree_eq (n : ℕ) (z ω : List Bool) (r : A.Coins n)
    (hist : QueryLog (bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)))
    (s : Fin (stateLen.eval n) → Bool) (b : ℕ) :
    iTree A dα din dout din' dout' stateLen perCall outLen finCall run advIn finRun n z ω r hist s b
        =
      (simulate (iImpl din dout din' dout' stateLen perCall run n z ω)
        (buildComp (advNext A (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n)
          (dα.eval n)) n (advIn (pairEncode (List.replicate n true) (pairEncode z ω))) r)
          (zeroBits _) b hist) s).bind
        fun res => iFinish din' dout' stateLen outLen finCall finRun n z ω res.2 res.1 :=
  rfl

section Phases

variable {A q dα din dout din' dout' stateLen perCall outLen finCall run advIn finRun}
  {n : ℕ} {z ω : List Bool} {r : A.Coins n} {init : Fin (stateLen.eval n) → Bool}

local notation "INNER" => bitSpec (fun i => PolyExpr.eval (din i) n) (fun i => PolyExpr.eval (dout
    i) n)
local notation "OUTER" => bitSpec (fun j => PolyExpr.eval (din' j) n) (fun j => PolyExpr.eval (dout'
    j) n)
local notation "CIN" => bitCodec (fun i => PolyExpr.eval (din i) n) (fun i => PolyExpr.eval (dout i)
    n)
  (PolyExpr.eval dα n)
local notation "COUT" => bitCodec (fun j => PolyExpr.eval (din' j) n) (fun j => PolyExpr.eval (dout'
    j) n)
  (PolyExpr.eval outLen n)
local notation "XOF" => iX A din' dout' stateLen outLen n z ω r init
local notation "INV" => IInv A q dα din dout din' dout' stateLen perCall outLen finCall run advIn
  finRun n z ω r init
local notation "NEXT" => iNext A q dα din dout din' dout' stateLen perCall outLen finCall run advIn
  finRun n z ω r init
local notation "ACT" => iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
local notation "BND" => iBound q dα din dout din' stateLen perCall finCall dout'
local notation "CTX" => pairEncode (List.replicate n true) (pairEncode z ω)
local notation "TREE" => iTree A dα din dout din' dout' stateLen perCall outLen finCall run advIn
  finRun n z ω r

/-- The parameter of the layout `iX O` is `1^n`. -/
theorem iX_inParam (O : QueryLog OUTER) : NUPPT.inParam (XOF O) = List.replicate n true := by
  rw [iX_eq, NUPPT.inParam_layout]

/-- The context read off the layout `iX O` is `⟨1^n, ⟨z, ω⟩⟩`. -/
theorem iX_ctx (O : QueryLog OUTER) : iCtx (XOF O) = CTX := by
  rw [iCtx_eq, iX_inParam, iX_eq, NUPPT.inArg_layout, pairFstD_pairEncode, pairFstD_pairEncode,
    pairSndD_pairEncode]

/-- The advice of the layout `iX O` is `⟨A.advice n, s₀⟩`. -/
theorem iX_inAdvice (O : QueryLog OUTER) :
    NUPPT.inAdvice (XOF O) = pairEncode (A.advice n) (List.ofFn init) := by
  rw [iX_eq, NUPPT.inAdvice_layout]

/-- The coins of the layout `iX O` are `A`'s coins `r`. -/
theorem iX_inCoins (O : QueryLog OUTER) : NUPPT.inCoins (XOF O) = List.ofFn r := by
  rw [iX_eq, NUPPT.inCoins_layout]

/-- The outer log read off the layout `iX O` is the encoding of `O`. -/
theorem iX_outer (O : QueryLog OUTER) : iOuter (XOF O) = (COUT).encodeLog O := by
  rw [iOuter_eq, iX_eq, NUPPT.inArg_layout, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The parameter is at most the length of the layout. -/
theorem le_length_iX (O : QueryLog OUTER) : n ≤ (XOF O).length := by
  rw [iX_eq]
  exact le_length_layout n _ _ _

/-- The encoded outer log is at most the length of the layout. -/
theorem length_encodeLog_le_iX (O : QueryLog OUTER) : ((COUT).encodeLog O).length ≤ (XOF O).length
    := by
  rw [iX_eq, NUPPT.layout_eq]
  simp only [length_pairEncode]
  omega

/-- A continuing round on every extension preserves the invariant (`runsTo_succ`). -/
theorem iInv_succ {t : ℕ} {P : QueryLog OUTER} {S S' : QueryLog OUTER → List Bool} (h : INV t P S)
    (hact : ∀ O', ACT (pairEncode (XOF (P ++ O')) (S O')) = pairEncode [false] (S' O'))
    (hb : ∀ O', (S' O').length ≤ (BND).eval (XOF (P ++ O')).length) : INV (t + 1) P S' :=
  fun O' => runsTo_succ (h O') (hact O') (hb O')

/-- **Replaying an entry:** if, on every extension `e :: O'`, the round continues with the state
`S' O'` (the entry `e` consumed), the invariant holds one round later with `e` replayed. -/
theorem iInv_consume {t : ℕ} {P : QueryLog OUTER} {S S' : QueryLog OUTER → List Bool}
    (e : Σ j, (OUTER).dom j × (OUTER).rng j) (h : INV t P S)
    (hact : ∀ O', ACT (pairEncode (XOF (P ++ e :: O')) (S (e :: O'))) = pairEncode [false] (S' O'))
    (hb : ∀ O', (S' O').length ≤ (BND).eval (XOF ((P ++ [e]) ++ O')).length) :
    INV (t + 1) (P ++ [e]) S' := by
  intro O'
  have hO : (P ++ [e]) ++ O' = P ++ e :: O' := by rw [List.append_assoc, List.singleton_append]
  have hb' := hb O'
  rw [hO] at hb' ⊢
  exact runsTo_succ (h (e :: O')) (hact O') hb'

/-- **A stopping round** on the replayed prefix `P` itself is the machine's next move on `P`
(`runsTo_stop`). -/
theorem iInv_stop {t : ℕ} {P : QueryLog OUTER} {S : QueryLog OUTER → List Bool} {W : List Bool}
    (h : INV t P S) (hact : ACT (pairEncode (XOF P) (S [])) = pairEncode [true] W)
    (ht : t ≤ (iRounds q perCall finCall).eval n) :
    NEXT P = decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (outLen.eval n) W
        := by
  have h0 := h []
  rw [List.append_nil] at h0
  rw [iNext_eq, iRaw_eq, runsTo_stop h0 hact
    (ht.trans ((iRounds q perCall finCall).eval_mono (le_length_iX P)))]

/-- **The typed state bound:** a state word built from an inner log of at most `q(n)` entries, the
handler's state, a budget of at most `q(n)`, and components within their bounds, is within
`iBound` on every layout extending the replayed prefix. -/
theorem iSt_le_iBound (P O' : QueryLog OUTER) (ph cur Lc cw : List Bool) (hist : QueryLog INNER)
    (s : Fin (stateLen.eval n) → Bool) (b : ℕ) (hph : ph.length ≤ 1) (hhist : hist.length ≤ q.eval
        n)
    (hb : b ≤ q.eval n) (hcur : cur.length ≤ (iCurBound dα din).eval n)
    (hLc : Lc.length ≤ (perCall.eval n + finCall.eval n) * (entryPoly din' dout').eval n)
    (hcw : cw.length ≤ perCall.eval n + finCall.eval n) :
    (iSt ph ((CIN).encodeLog hist) (List.ofFn s) (List.replicate b true) cur Lc cw
      ((COUT).encodeLog O')).length ≤ (BND).eval (XOF (P ++ O')).length :=
  length_iSt_le q dα din dout din' dout' stateLen perCall finCall (le_length_iX _) hph
    ((length_encodeLog_le CIN _ hist (fun e _ => entry_le_entryPoly din dout n e _)).trans
      (Nat.mul_le_mul_right _ hhist))
    (by rw [List.length_ofFn]) (by rw [List.length_replicate]; exact hb) hcur hLc hcw
    ((length_encodeLog_le_append COUT O' P).trans (length_encodeLog_le_iX _))

/-- An outer log of at most `c` entries is at most `c · E'` bits. -/
theorem outLog_le (L : QueryLog OUTER) {c : ℕ} (hL : L.length ≤ c) :
    ((COUT).encodeLog L).length ≤ c * (entryPoly din' dout').eval n :=
  (length_encodeLog_le COUT _ L (fun e _ => entry_le_entryPoly din' dout' n e _)).trans
    (Nat.mul_le_mul_right _ hL)

/-- A pending inner query `⟨1^i, x⟩` is within the bound `iCurBound`. -/
theorem query_le_iCurBound (i : Fin k) (x : Fin ((din i).eval n) → Bool) :
    (pairEncode (List.replicate i true) (List.ofFn x)).length ≤ (iCurBound dα din).eval n := by
  rw [length_pairEncode, List.length_replicate, List.length_ofFn, iCurBound_eq]
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  have h1 := i.isLt
  have h2 := eval_le_sumPoly din i n
  omega

/-- An adversary's output is within the bound `iCurBound`. -/
theorem output_le_iCurBound (a : Fin (dα.eval n) → Bool) :
    (List.ofFn a).length ≤ (iCurBound dα din).eval n := by
  rw [List.length_ofFn, iCurBound_eq]
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  omega

/-- The adversary's move word on the layout `iX O` and a state word with log `hist` is the
canonical word of its next move (`canonWord_eq`). -/
theorem iAdvMove_iX (O : QueryLog OUTER) (hist : QueryLog INNER) (sw bw cur Lc cw Ow : List Bool) :
    iAdvMove A dα din advIn (pairEncode (XOF O) (iSt [] ((CIN).encodeLog hist) sw bw cur Lc cw Ow))
        =
      encodeBitMove (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n)
        (advNext A CIN n (advIn CTX) r hist) := by
  rw [iAdvMove_iSt A dα din advIn (iX_inParam O), iX_ctx, iX_inAdvice, iX_inCoins,
    pairFstD_pairEncode, ← NUPPT.runAtL_eq_output_layout, ← NUPPT.runAt_eq,
    canonWord_eq din (fun i => (dout i).eval n), advNext_eq, bitCodec_decodeMove]

/-- The handler's move word in a call on the layout `iX O` is the canonical word of the call's
next move (`canonWord_eq`, `encodeLog_bitCodec`). -/
theorem iCallMove_iX (O : QueryLog OUTER) (ph Lin : List Bool) (s : Fin (stateLen.eval n) → Bool)
    (bw : List Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool) (L : QueryLog OUTER)
    (cw Ow : List Bool) :
    iCallMove dout din' stateLen run (pairEncode (XOF O) (iSt ph Lin (List.ofFn s) bw
        (pairEncode (List.replicate i true) (List.ofFn x)) ((COUT).encodeLog L) cw Ow)) =
      encodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
        ((dout i).eval n + stateLen.eval n)
        (iCallNext din dout din' dout' stateLen run n z ω s i x L) := by
  rw [iCallMove_iSt dout din' stateLen run (iX_inParam O), iX_ctx, List.length_replicate, selLen_eq,
    encodeLog_bitCodec _ _ (outLen.eval n) 0 L, canonWord_eq din' (fun j => (dout' j).eval n),
    iCallNext_eq]

/-- The finalization's move word on the layout `iX O` is the canonical word of its next move. -/
theorem iFinMove_iX (O : QueryLog OUTER) (ph Lin : List Bool) (s : Fin (stateLen.eval n) → Bool)
    (bw : List Bool) {d : ℕ} (a : Fin d → Bool) (L : QueryLog OUTER) (cw Ow : List Bool) :
    iFinMove din' outLen finRun (pairEncode (XOF O) (iSt ph Lin (List.ofFn s) bw (List.ofFn a)
        ((COUT).encodeLog L) cw Ow)) =
      encodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (outLen.eval n)
        (iFinNext din' dout' stateLen outLen finRun n z ω s a L) := by
  rw [iFinMove_iSt din' outLen finRun (iX_inParam O), iX_ctx,
    encodeLog_bitCodec _ _ (outLen.eval n) 0 L, canonWord_eq din' (fun j => (dout' j).eval n),
    iFinNext_eq]

/-- **The finalization is replayed.** From a state word of the finalization with outer log `L`
and remaining budget `c`, reached after `t` rounds on every extension of the replayed prefix `P`,
the machine's next-move function replays `buildComp` of the finalization's rounds.

**Proof sketch.** Induction on `c`. The finalization's move word is the canonical word of its
next move (`iFinMove_iX`). An output `W` stops the machine with the word `⟨[true], W⟩`
(`iAct_fin_ret`, `iInv_stop`). A query at budget `0` stops it with the default
(`iAct_fin_timeout`). A query within budget is, on the prefix itself, the machine's next move
(`iAct_fin_stop`); on an extension by an entry with answer `y`, the entry is replayed
(`iAct_fin_ask`, `iInv_consume`, `encodeLog_append_single`) and the induction hypothesis applies to
the continuation. -/
theorem fin_phase (hist : QueryLog INNER) (s : Fin (stateLen.eval n) → Bool) (b : ℕ)
    (a : Fin (dα.eval n) → Bool) (hhist : hist.length ≤ q.eval n) (hb : b ≤ q.eval n) :
    ∀ (c : ℕ) (L : QueryLog OUTER) (t : ℕ) (P : QueryLog OUTER), L.length + c = finCall.eval n →
      INV t P (fun O' => iSt [false] ((CIN).encodeLog hist) (List.ofFn s) (List.replicate b true)
        (List.ofFn a) ((COUT).encodeLog L) (List.replicate c true) ((COUT).encodeLog O')) →
      t + c + 1 ≤ (iRounds q perCall finCall).eval n →
      ReplaysFrom (buildComp (iFinNext din' dout' stateLen outLen finRun n z ω s a) (zeroBits _) c
          L)
        (fun O' => NEXT (P ++ O')) := by
  intro c
  induction c with
  | zero =>
    intro L t P hL hinv ht
    cases hm : iFinNext din' dout' stateLen outLen finRun n z ω s a L with
    | ret W =>
      have hact : ACT (pairEncode (XOF P) (iSt [false] ((CIN).encodeLog hist) (List.ofFn s)
          (List.replicate b true) (List.ofFn a) ((COUT).encodeLog L) (List.replicate 0 true)
          ((COUT).encodeLog []))) = pairEncode [true] (pairEncode [true] (List.ofFn W)) :=
        iAct_fin_ret _ _ _ _ _ _ _ _ _ _ _ _ (by rw [iFinMove_iX, hm, encodeBitMove_ret])
      rw [buildComp_zero_of_ret hm, replaysFrom_pure_iff, List.append_nil,
        iInv_stop hinv hact (by omega), decodeBitMove_ret]
    | query j x' =>
      have hact : ACT (pairEncode (XOF P) (iSt [false] ((CIN).encodeLog hist) (List.ofFn s)
          (List.replicate b true) (List.ofFn a) ((COUT).encodeLog L) (List.replicate 0 true)
          ((COUT).encodeLog []))) =
          pairEncode [true] (pairEncode [true] (List.ofFn (zeroBits (outLen.eval n)))) := by
        rw [List.replicate_zero, ofFn_zeroBits]
        exact iAct_fin_timeout _ _ _ _ _ _ _ _ _ _ _ _ (iX_inParam P)
          (by rw [iFinMove_iX, hm, encodeBitMove_query])
      rw [buildComp_zero_of_query hm, replaysFrom_pure_iff, List.append_nil,
        iInv_stop hinv hact (by omega), decodeBitMove_ret]
  | succ c ih =>
    intro L t P hL hinv ht
    cases hm : iFinNext din' dout' stateLen outLen finRun n z ω s a L with
    | ret W =>
      have hact : ACT (pairEncode (XOF P) (iSt [false] ((CIN).encodeLog hist) (List.ofFn s)
          (List.replicate b true) (List.ofFn a) ((COUT).encodeLog L) (List.replicate (c + 1) true)
          ((COUT).encodeLog []))) = pairEncode [true] (pairEncode [true] (List.ofFn W)) :=
        iAct_fin_ret _ _ _ _ _ _ _ _ _ _ _ _ (by rw [iFinMove_iX, hm, encodeBitMove_ret])
      rw [buildComp_succ_of_ret hm, replaysFrom_pure_iff, List.append_nil,
        iInv_stop hinv hact (by omega), decodeBitMove_ret]
    | query j x' =>
      rw [buildComp_succ_of_query hm, replaysFrom_query_iff]
      refine ⟨?_, fun y => ?_⟩
      · have hact : ACT (pairEncode (XOF P) (iSt [false] ((CIN).encodeLog hist) (List.ofFn s)
            (List.replicate b true) (List.ofFn a) ((COUT).encodeLog L) (List.replicate (c + 1) true)
            ((COUT).encodeLog []))) = pairEncode [true] (pairEncode [false]
              (pairEncode (List.replicate j true) (List.ofFn x'))) := by
          rw [List.replicate_succ, MachineCodec.encodeLog_nil]
          exact iAct_fin_stop _ _ _ _ _ _ _ _ _ _ _ _
            (by rw [iFinMove_iX, hm, encodeBitMove_query])
        rw [List.append_nil, iInv_stop hinv hact (by omega), decodeBitMove_query]
      · have hinv' : INV (t + 1) (P ++ [⟨j, x', y⟩]) (fun O' => iSt [false] ((CIN).encodeLog hist)
            (List.ofFn s) (List.replicate b true) (List.ofFn a)
            ((COUT).encodeLog (L ++ [⟨j, x', y⟩])) (List.replicate c true) ((COUT).encodeLog O')) :=
                by
          intro O'
          have hb0 := iSt_le_iBound (A := A) (q := q) (dα := dα) (din := din) (dout := dout)
              (din' := din') (dout' := dout') (stateLen := stateLen) (perCall := perCall)
              (outLen := outLen) (finCall := finCall) (r := r) (init := init) (z := z) (ω := ω)
            (P ++ [⟨j, x', y⟩]) O' [false] (List.ofFn a) ((COUT).encodeLog (L ++ [⟨j, x', y⟩]))
            (List.replicate c true) hist s b (by decide) hhist hb (output_le_iCurBound a)
            (outLog_le _ (by rw [List.length_append, List.length_singleton]; omega))
            (by rw [List.length_replicate]; omega)
          rw [List.append_assoc, List.singleton_append] at hb0 ⊢
          refine runsTo_succ (hinv (⟨j, x', y⟩ :: O')) ?_ hb0
          beta_reduce
          rw [List.replicate_succ, MachineCodec.encodeLog_cons, encodeLog_append_single]
          exact iAct_fin_ask _ _ _ _ _ _ _ _ _ _ _ _ (by rw [iFinMove_iX, hm, encodeBitMove_query])
        have h := ih _ (t + 1) _ (by rw [List.length_append, List.length_singleton]; omega) hinv'
          (by omega)
        simp only [List.append_assoc, List.singleton_append] at h
        exact h


/-- **A call is replayed.** From a state word of a call on the inner query `x` to oracle `i`,
with outer log `L` and remaining budget `c`, the machine's next-move function replays `buildComp`
of the call's rounds followed by the rest of the reduction, given that the rest of the reduction
is replayed from every state word of the adversary after the call (`K`).

**Proof sketch.** Induction on `c`. The handler's move word is the canonical word of the call's
next move (`iCallMove_iX`). An answer `W = y ‖ s'`, or the joint default at budget `0`, ends the
call (`iAct_call_ret`, `iAct_call_timeout`, `iCallEnd_iSt`): the entry `⟨i, x, y⟩` is appended to
the adversary's log (`ofFn_take_drop_add`, `encodeLog_append_single`) and `K` applies, after the
monad law `pure_bind`. A query within budget is replayed as in the finalization (`iAct_call_stop`,
`iAct_call_ask`, `iInv_consume`, `query_bind`). -/
theorem call_phase (hist : QueryLog INNER) (s : Fin (stateLen.eval n) → Bool) (b : ℕ) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) (hlen : hist.length + b + 1 = q.eval n)
    (K : ∀ (y : Fin ((dout i).eval n) → Bool) (s' : Fin (stateLen.eval n) → Bool) (t : ℕ)
      (P : QueryLog OUTER),
      INV t P (fun O' => iSt [] ((CIN).encodeLog (hist ++ [⟨i, x, y⟩])) (List.ofFn s')
        (List.replicate b true) [] [] [] ((COUT).encodeLog O')) →
      t + (2 + finCall.eval n + b * (perCall.eval n + 2)) ≤ (iRounds q perCall finCall).eval n →
      ReplaysFrom (TREE (hist ++ [⟨i, x, y⟩]) s' b) (fun O' => NEXT (P ++ O'))) :
    ∀ (c : ℕ) (L : QueryLog OUTER) (t : ℕ) (P : QueryLog OUTER), L.length + c = perCall.eval n →
      INV t P (fun O' => iSt [true] ((CIN).encodeLog hist) (List.ofFn s) (List.replicate b true)
        (pairEncode (List.replicate i true) (List.ofFn x)) ((COUT).encodeLog L)
        (List.replicate c true) ((COUT).encodeLog O')) →
      t + c + 1 + (2 + finCall.eval n + b * (perCall.eval n + 2)) ≤
        (iRounds q perCall finCall).eval n →
      ReplaysFrom ((buildComp (iCallNext din dout din' dout' stateLen run n z ω s i x) (zeroBits _)
          c
          L).bind fun w => TREE (hist ++ [⟨i, x, fun j => w (Fin.castAdd (stateLen.eval n) j)⟩])
            (fun j => w (Fin.natAdd ((dout i).eval n) j)) b)
        (fun O' => NEXT (P ++ O')) := by
  -- The end of a call with the result `w`, at any budget word `cw`.
  have hend : ∀ (t : ℕ) (P : QueryLog OUTER) (L : QueryLog OUTER) (cw : List Bool)
      (w : Fin ((dout i).eval n + stateLen.eval n) → Bool),
      INV t P (fun O' => iSt [true] ((CIN).encodeLog hist) (List.ofFn s) (List.replicate b true)
        (pairEncode (List.replicate i true) (List.ofFn x)) ((COUT).encodeLog L) cw
        ((COUT).encodeLog O')) →
      (∀ O', ACT (pairEncode (XOF (P ++ O')) (iSt [true] ((CIN).encodeLog hist) (List.ofFn s)
        (List.replicate b true) (pairEncode (List.replicate i true) (List.ofFn x))
        ((COUT).encodeLog L) cw ((COUT).encodeLog O'))) =
        pairEncode [false] (iCallEnd dout (pairEncode (XOF (P ++ O')) (iSt [true]
          ((CIN).encodeLog hist) (List.ofFn s) (List.replicate b true)
          (pairEncode (List.replicate i true) (List.ofFn x)) ((COUT).encodeLog L) cw
          ((COUT).encodeLog O'))) (List.ofFn w))) →
      t + 1 + (2 + finCall.eval n + b * (perCall.eval n + 2)) ≤ (iRounds q perCall finCall).eval n →
      ReplaysFrom (TREE (hist ++ [⟨i, x, fun j => w (Fin.castAdd (stateLen.eval n) j)⟩])
        (fun j => w (Fin.natAdd ((dout i).eval n) j)) b) (fun O' => NEXT (P ++ O')) := by
    intro t P L cw w hinv hact ht
    refine K _ _ (t + 1) P (fun O' => ?_) ht
    refine runsTo_succ (hinv O') ?_ ?_
    · beta_reduce
      rw [hact, iCallEnd_iSt dout (iX_inParam _), List.length_replicate, selLen_eq,
        (ofFn_take_drop_add w).1, (ofFn_take_drop_add w).2, encodeLog_append_single,
        bitCodec_encodeEntry]
    · exact iSt_le_iBound (A := A) (q := q) (dα := dα) (din := din) (dout := dout) (din' := din')
        (dout' := dout') (stateLen := stateLen) (perCall := perCall) (outLen := outLen)
        (finCall := finCall) (r := r) (init := init) (z := z) (ω := ω)
        P O' [] [] [] [] _ _ b (by decide)
            (by rw [List.length_append, List.length_singleton]; omega) (by omega) (Nat.zero_le _)
        (Nat.zero_le _) (Nat.zero_le _)
  intro c
  induction c with
  | zero =>
    intro L t P hL hinv ht
    cases hm : iCallNext din dout din' dout' stateLen run n z ω s i x L with
    | ret W =>
      rw [buildComp_zero_of_ret hm, OracleComp.pure_bind]
      refine hend t P L _ W hinv (fun O' => ?_) (by omega)
      exact iAct_call_ret _ _ _ _ _ _ _ _ _ _ _ _ (by rw [iCallMove_iX, hm, encodeBitMove_ret])
    | query j x' =>
      rw [buildComp_zero_of_query hm, OracleComp.pure_bind]
      refine hend t P L _ (zeroBits _) hinv (fun O' => ?_) (by omega)
      have hact : ACT (pairEncode (XOF (P ++ O')) (iSt [true] ((CIN).encodeLog hist) (List.ofFn s)
          (List.replicate b true) (pairEncode (List.replicate i true) (List.ofFn x))
          ((COUT).encodeLog L) [] ((COUT).encodeLog O'))) =
          pairEncode [false] (iCallEnd dout (pairEncode (XOF (P ++ O')) (iSt [true]
            ((CIN).encodeLog hist) (List.ofFn s) (List.replicate b true)
            (pairEncode (List.replicate i true) (List.ofFn x)) ((COUT).encodeLog L) []
            ((COUT).encodeLog O')))
            (List.replicate (selLen dout n (List.replicate (↑i) true).length + stateLen.eval n)
              false)) :=
        iAct_call_timeout _ _ _ _ _ _ _ _ _ _ _ _ (iX_inParam _)
          (by rw [iCallMove_iX, hm, encodeBitMove_query])
      rw [List.length_replicate, selLen_eq, ← ofFn_zeroBits] at hact
      rw [List.replicate_zero]
      exact hact
  | succ c ih =>
    intro L t P hL hinv ht
    cases hm : iCallNext din dout din' dout' stateLen run n z ω s i x L with
    | ret W =>
      rw [buildComp_succ_of_ret hm, OracleComp.pure_bind]
      refine hend t P L _ W hinv (fun O' => ?_) (by omega)
      exact iAct_call_ret _ _ _ _ _ _ _ _ _ _ _ _ (by rw [iCallMove_iX, hm, encodeBitMove_ret])
    | query j x' =>
      rw [buildComp_succ_of_query hm, OracleComp.query_bind, replaysFrom_query_iff]
      refine ⟨?_, fun y => ?_⟩
      · have hact : ACT (pairEncode (XOF P) (iSt [true] ((CIN).encodeLog hist) (List.ofFn s)
            (List.replicate b true) (pairEncode (List.replicate i true) (List.ofFn x))
            ((COUT).encodeLog L) (List.replicate (c + 1) true) ((COUT).encodeLog []))) =
            pairEncode [true] (pairEncode [false]
              (pairEncode (List.replicate j true) (List.ofFn x'))) := by
          rw [List.replicate_succ, MachineCodec.encodeLog_nil]
          exact iAct_call_stop _ _ _ _ _ _ _ _ _ _ _ _
            (by rw [iCallMove_iX, hm, encodeBitMove_query])
        rw [List.append_nil, iInv_stop hinv hact (by omega), decodeBitMove_query]
      · have hinv' : INV (t + 1) (P ++ [⟨j, x', y⟩]) (fun O' => iSt [true] ((CIN).encodeLog hist)
            (List.ofFn s) (List.replicate b true) (pairEncode (List.replicate i true) (List.ofFn x))
            ((COUT).encodeLog (L ++ [⟨j, x', y⟩])) (List.replicate c true) ((COUT).encodeLog O')) :=
                by
          intro O'
          have hb0 := iSt_le_iBound (A := A) (q := q) (dα := dα) (din := din) (dout := dout)
              (din' := din') (dout' := dout') (stateLen := stateLen) (perCall := perCall)
              (outLen := outLen) (finCall := finCall) (r := r) (init := init) (z := z) (ω := ω)
            (P ++ [⟨j, x', y⟩]) O' [true] (pairEncode (List.replicate i true) (List.ofFn x))
            ((COUT).encodeLog (L ++ [⟨j, x', y⟩])) (List.replicate c true) hist s b (by decide)
            (by omega) (by omega) (query_le_iCurBound i x)
            (outLog_le _ (by rw [List.length_append, List.length_singleton]; omega))
            (by rw [List.length_replicate]; omega)
          rw [List.append_assoc, List.singleton_append] at hb0 ⊢
          refine runsTo_succ (hinv (⟨j, x', y⟩ :: O')) ?_ hb0
          beta_reduce
          rw [List.replicate_succ, MachineCodec.encodeLog_cons, encodeLog_append_single]
          exact iAct_call_ask _ _ _ _ _ _ _ _ _ _ _ _
              (by rw [iCallMove_iX, hm, encodeBitMove_query])
        have h := ih _ (t + 1) _ (by rw [List.length_append, List.length_singleton]; omega) hinv'
          (by omega)
        simp only [List.append_assoc, List.singleton_append] at h
        exact h

/-- **The rest of the reduction is replayed.** From a state word of the adversary with log
`hist` and remaining budget `b` (with `|hist| + b = q(n)`), reached after `t` rounds on every
extension of the replayed prefix `P`, the machine's next-move function replays `iTree`.

**Proof sketch.** Induction on `b`. The adversary's move word is the canonical word of its next
move (`iAdvMove_iX`). An output `a`, or a query at budget `0` (output `0^{dα(n)}`), opens the
finalization (`iAct_adv_ret`, `iAct_adv_timeout`), and `fin_phase` applies after
`buildComp_*_of_ret`/`_of_query`, `simulate_pure` and `pure_bind`. A query `x` to oracle `i`
within budget opens a call (`iAct_adv_query`); the simulation unfolds into the call followed by
the rest of the reduction (`simulate_query`, `iImpl_apply`, `bind_assoc`, `pure_bind`), and
`call_phase` applies with the induction hypothesis as its continuation. The round count decreases
along the way: `2 + finCall + b (perCall + 2)` rounds suffice. -/
theorem adv_phase : ∀ (b : ℕ) (hist : QueryLog INNER) (s : Fin (stateLen.eval n) → Bool) (t : ℕ)
    (P : QueryLog OUTER), hist.length + b = q.eval n →
    INV t P (fun O' => iSt [] ((CIN).encodeLog hist) (List.ofFn s) (List.replicate b true) [] [] []
      ((COUT).encodeLog O')) →
    t + (2 + finCall.eval n + b * (perCall.eval n + 2)) ≤ (iRounds q perCall finCall).eval n →
    ReplaysFrom (TREE hist s b) (fun O' => NEXT (P ++ O')) := by
  -- Opening the finalization with the adversary's output `a`.
  have hfin : ∀ (b : ℕ) (hist : QueryLog INNER) (s : Fin (stateLen.eval n) → Bool) (t : ℕ)
      (P : QueryLog OUTER) (a : Fin (dα.eval n) → Bool), hist.length + b = q.eval n →
      INV t P (fun O' => iSt [] ((CIN).encodeLog hist) (List.ofFn s) (List.replicate b true) [] []
          []
        ((COUT).encodeLog O')) →
      (∀ O', ACT (pairEncode (XOF (P ++ O')) (iSt [] ((CIN).encodeLog hist) (List.ofFn s)
        (List.replicate b true) [] [] [] ((COUT).encodeLog O'))) =
        pairEncode [false] (iSt [false] ((CIN).encodeLog hist) (List.ofFn s) (List.replicate b true)
          (List.ofFn a) ((COUT).encodeLog []) (List.replicate (finCall.eval n) true)
          ((COUT).encodeLog O'))) →
      t + 1 + (finCall.eval n) + 1 ≤ (iRounds q perCall finCall).eval n →
      ReplaysFrom (iFinish din' dout' stateLen outLen finCall finRun n z ω s a)
        (fun O' => NEXT (P ++ O')) := by
    intro b hist s t P a hlen hinv hact ht
    rw [iFinish_eq_buildComp]
    refine fin_phase hist s b a (by omega) (by omega) (finCall.eval n) [] (t + 1) P
      (by rw [List.length_nil, Nat.zero_add]) (fun O' => ?_) ht
    exact runsTo_succ (hinv O') (hact O') (iSt_le_iBound (A := A) (q := q) (dα := dα) (din := din)
        (dout := dout) (din' := din') (dout' := dout') (stateLen := stateLen) (perCall := perCall)
        (outLen := outLen) (finCall := finCall) (r := r) (init := init) (z := z) (ω := ω)
      P O' [false] (List.ofFn a) ((COUT).encodeLog [])
      (List.replicate (finCall.eval n) true) hist s b (by decide) (by omega) (by omega)
      (output_le_iCurBound a) (by rw [MachineCodec.encodeLog_nil]; exact Nat.zero_le _)
      (by rw [List.length_replicate]; omega))
  intro b
  induction b with
  | zero =>
    intro hist s t P hlen hinv ht
    cases hm : advNext A CIN n (advIn CTX) r hist with
    | ret a =>
      rw [iTree_eq, buildComp_zero_of_ret hm, simulate_pure, OracleComp.pure_bind]
      refine hfin 0 hist s t P a hlen hinv (fun O' => ?_) (by omega)
      rw [MachineCodec.encodeLog_nil]
      exact iAct_adv_ret _ _ _ _ _ _ _ _ _ _ _ _ (iX_inParam _)
        (by rw [iAdvMove_iX, hm, encodeBitMove_ret])
    | query i x =>
      rw [iTree_eq, buildComp_zero_of_query hm, simulate_pure, OracleComp.pure_bind]
      refine hfin 0 hist s t P _ hlen hinv (fun O' => ?_) (by omega)
      rw [MachineCodec.encodeLog_nil, List.replicate_zero, ofFn_zeroBits]
      exact iAct_adv_timeout _ _ _ _ _ _ _ _ _ _ _ _ (iX_inParam _)
        (by rw [iAdvMove_iX, hm, encodeBitMove_query])
  | succ b ih =>
    intro hist s t P hlen hinv ht
    cases hm : advNext A CIN n (advIn CTX) r hist with
    | ret a =>
      rw [iTree_eq, buildComp_succ_of_ret hm, simulate_pure, OracleComp.pure_bind]
      refine hfin (b + 1) hist s t P a hlen hinv (fun O' => ?_) (by rw [Nat.add_mul] at ht; omega)
      rw [MachineCodec.encodeLog_nil]
      exact iAct_adv_ret _ _ _ _ _ _ _ _ _ _ _ _ (iX_inParam _)
        (by rw [iAdvMove_iX, hm, encodeBitMove_ret])
    | query i x =>
      rw [iTree_eq, buildComp_succ_of_query hm, simulate_query, iImpl_apply]
      simp only [OracleComp.bind_assoc, OracleComp.pure_bind]
      rw [iCall_eq_buildComp]
      refine call_phase hist s b i x (by omega)
        (fun y s' t' P' hinv' ht' => ih _ s' t' P'
          (by rw [List.length_append, List.length_singleton]; omega) hinv' ht')
        (perCall.eval n) [] (t + 1) P (by rw [List.length_nil, Nat.zero_add])
        (fun O' => ?_) (by rw [Nat.add_mul] at ht; omega)
      refine runsTo_succ (hinv O') ?_ (iSt_le_iBound (A := A) (q := q) (dα := dα) (din := din)
          (dout := dout) (din' := din') (dout' := dout') (stateLen := stateLen) (perCall := perCall)
          (outLen := outLen) (finCall := finCall) (r := r) (init := init) (z := z) (ω := ω)
        P O' [true] (pairEncode (List.replicate i true) (List.ofFn x))
        ((COUT).encodeLog []) (List.replicate (perCall.eval n) true) hist s b (by decide) (by omega)
        (by omega) (query_le_iCurBound i x)
            (by rw [MachineCodec.encodeLog_nil]; exact Nat.zero_le _)
        (by rw [List.length_replicate]; omega))
      beta_reduce
      rw [MachineCodec.encodeLog_nil, List.replicate_succ]
      exact iAct_adv_query _ _ _ _ _ _ _ _ _ _ _ _ (iX_inParam _)
        (by rw [iAdvMove_iX, hm, encodeBitMove_query])

end Phases

/-- **The functional equation of the replay machine.** At parameter `n`, with the reduction's
input `z`, seed `ω`, the adversary's coins `r` and the initial state `s₀`, the computation of the
next-move function `O ↦ decodeBitMove (iRaw (iX O))` with budget `q(n) · perCall(n) + finCall(n)`
is the simulation of `A` on `advIn ⟨1^n, ⟨z, ω⟩⟩` by the handler, followed by the finalization.

**Proof sketch.** The reduction tree is `iTree [] s₀ q(n)` (`toCompOn_eq_advNext`). It makes at
most `q(n) · perCall(n) + finCall(n)` queries: `A` makes at most `q(n)` (`toCompOn_costBoundedBy`),
each answered by at most `perCall(n)` outer queries (`buildComp_costBoundedBy`,
`costBoundedBy_mul`, `simulate_costBoundedBy`), and the finalization makes at most `finCall(n)`
(`CostBoundedBy.bind`). The machine's next-move function replays it from the empty log
(`adv_phase` from the initial state, `runsTo_zero`), so `buildComp_of_replaysFrom` gives the
equality of trees. -/
theorem iRaw_spec (n : ℕ) (z ω : List Bool) (r : A.Coins n) (init : Fin (stateLen.eval n) → Bool) :
    buildComp (fun O => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
        (outLen.eval n) (iRaw A q dα din dout din' stateLen perCall outLen finCall run advIn finRun
            dout'
          (iX A din' dout' stateLen outLen n z ω r init O)))
      (zeroBits _) (q.eval n * perCall.eval n + finCall.eval n) [] =
      (simulate (iImpl din dout din' dout' stateLen perCall run n z ω)
          (A.toCompOn (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
            n (q.eval n) (advIn (pairEncode (List.replicate n true) (pairEncode z ω))) r) init).bind
        fun res => iFinish din' dout' stateLen outLen finCall finRun n z ω res.2 res.1 := by
  have hT : (simulate (iImpl din dout din' dout' stateLen perCall run n z ω)
      (A.toCompOn (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
        n (q.eval n) (advIn (pairEncode (List.replicate n true) (pairEncode z ω))) r) init).bind
      (fun res => iFinish din' dout' stateLen outLen finCall finRun n z ω res.2 res.1) =
      iTree A dα din dout din' dout' stateLen perCall outLen finCall run advIn finRun n z ω r []
        init (q.eval n) := by
    rw [toCompOn_eq_advNext, bitCodec_timeout, iTree_eq]
  rw [hT]
  -- The reduction makes at most `q · perCall + finCall` queries.
  have hcost : (iTree A dα din dout din' dout' stateLen perCall outLen finCall run advIn finRun n z
      ω r
      [] init (q.eval n)).CostBoundedBy (fun _ => 1) (q.eval n * perCall.eval n + finCall.eval n) :=
          by
    rw [← hT]
    have himpl : ∀ i x s, OracleComp.CostBoundedBy (fun _ => 1)
        (iImpl din dout din' dout' stateLen perCall run n z ω i x s) ((fun _ => perCall.eval n) i)
            := by
      intro i x s
      have h := (buildComp_costBoundedBy (iCallNext din dout din' dout' stateLen run n z ω s i x)
        (zeroBits _) (perCall.eval n) []).bind
        (f := fun w => OracleComp.pure (spec := bitSpec (fun j => (din' j).eval n)
          (fun j => (dout' j).eval n))
          ((fun j => w (Fin.castAdd (stateLen.eval n) j), fun j => w (Fin.natAdd ((dout i).eval n)
              j)) :
            (Fin ((dout i).eval n) → Bool) × (Fin (stateLen.eval n) → Bool)))
        (q₂ := 0) (fun _ => OracleComp.costBoundedBy_pure _ _ _)
      rw [Nat.add_zero] at h
      rw [iImpl_apply, iCall_eq_buildComp]
      exact h
    have hA := costBoundedBy_mul (NUPPT.toCompOn_costBoundedBy A
      (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n)) n (q.eval n)
      (advIn (pairEncode (List.replicate n true) (pairEncode z ω))) r) (perCall.eval n)
    exact (simulate_costBoundedBy himpl hA init).bind fun res => by
      rw [iFinish_eq_buildComp]
      exact buildComp_costBoundedBy _ _ _ _
  -- The machine replays the reduction from the empty log.
  have hinv : IInv A q dα din dout din' dout' stateLen perCall outLen finCall run advIn finRun
      n z ω r init 0 [] (fun O' => iSt []
        ((bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n)).encodeLog [])
        (List.ofFn init) (List.replicate (q.eval n) true) [] [] []
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
          (outLen.eval n)).encodeLog O')) := by
    intro O'
    have hs : iStart q (iX A din' dout' stateLen outLen n z ω r init ([] ++ O')) = iSt []
        ((bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n)).encodeLog [])
        (List.ofFn init) (List.replicate (q.eval n) true) [] [] []
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
          (outLen.eval n)).encodeLog O') := by
      rw [iStart_eq, iX_inAdvice, pairSndD_pairEncode, iX_inParam, List.length_replicate, iX_outer,
        List.nil_append, MachineCodec.encodeLog_nil]
    beta_reduce
    rw [← hs]
    exact runsTo_zero (by
      rw [hs]
      exact iSt_le_iBound (A := A) (q := q) (dα := dα) (din := din) (dout := dout) (din' := din')
          (dout' := dout') (stateLen := stateLen) (perCall := perCall) (outLen := outLen)
          (finCall := finCall) (r := r) (init := init) (z := z) (ω := ω)
        [] O' [] [] [] [] [] init (q.eval n) (by decide) (Nat.zero_le _) le_rfl
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _))
  have hrep := adv_phase (A := A) (q := q) (dα := dα) (din := din) (dout := dout) (din' := din')
    (dout' := dout') (stateLen := stateLen) (perCall := perCall) (outLen := outLen)
    (finCall := finCall) (run := run) (advIn := advIn) (finRun := finRun) (init := init)
    (q.eval n) [] init 0 [] (by rw [List.length_nil, Nat.zero_add]) hinv (by
      rw [iRounds_eq]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
      omega)
  exact buildComp_of_replaysFrom _ _ _ [] _ hrep hcost
end Spec

end TCSlib.Cryptography.Games.EffFill
