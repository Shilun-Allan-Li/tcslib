/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Bridges.QueryTree
import TCSlib.Cryptography.Asymptotic.PRF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as oracle computations

The asymptotic layer quantifies over non-uniform probabilistic polynomial-time machines
(`Complexity.NUPPT`). A machine interacts with oracles as a **next-move function**: at
parameter `n`, with one random tape `r` for the whole interaction, it is run on the encoding of the
queries and answers so far. Its output is decoded as the next move: a query to one of the
oracles, or the final output. A query budget `q` ends the interaction (D7 of the ch. 2–4 design:
no oracle tapes, one activation per query).

This file turns such a machine into an oracle computation of the `Games` framework
(`NUPPT.toComp`), for any oracle family and any output type, given a *codec*: how output strings
decode into moves, and how a query-log entry encodes as a string. The ch. 2–4 layer's
`NUPPT.toOracleAdversary` (one oracle, a Boolean verdict) is the instance with the codec built
from its own `decodeOracleMove` and `encodeHist` (`toComp_singleCodec`).

The efficiency counterpart (a reduction written as an implementation of polynomial-time
computable handlers, run on a machine, is again a machine's computation) is the S2b efficiency
result, stated in a later module.

## Main definitions

* `Games.Move spec α`: a query to an oracle of `spec`, or a final output in `α`.
* `Games.MachineCodec spec α`: decoding of moves and encoding of log entries.
* `Games.buildComp next timeout q hist`: the computation of a next-move function with budget `q`.
* `Complexity.NUPPT.toComp D codec n q r`: the computation of the machine `D` at parameter `n`
  with coins `r`.
* `Games.singleCodec ℓ₁ ℓ₂`: the codec of the ch. 2–4 next-query machines.

## Main results

* `Games.buildComp_costBoundedBy`: the computation makes at most `q` queries.
* `Games.toComp_singleCodec`: `toOracleAdversary` is the one-oracle instance of `toComp`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 and Definition 96.1 (oracle machines).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

open Complexity Turing

variable {ι : Type} {α : Type}

/-- A **move** of a next-move machine against the oracles of `spec`: ask oracle `i` the query
`x`, or stop with the output `a`. -/
inductive Move (spec : OracleSpec ι) (α : Type) : Type where
  /-- Ask oracle `i` the query `x`. -/
  | query (i : ι) (x : spec.dom i)
  /-- Stop with the output `a`. -/
  | ret (a : α)

/-- A **codec** for machines against `spec` with outputs in `α`: how an output string decodes
into a move, how one query-log entry is encoded for the machine, and the output forced when the
query budget runs out. -/
structure MachineCodec (spec : OracleSpec ι) (α : Type) where
  /-- Decode a machine output as a move. -/
  decodeMove : List Bool → Move spec α
  /-- Encode one log entry (oracle, query, answer). -/
  encodeEntry : (Σ i, spec.dom i × spec.rng i) → List Bool
  /-- The output when the budget is exhausted. -/
  timeout : α

namespace MachineCodec

variable {spec : OracleSpec ι}

/-- The encoding of a query log handed to the machine: the nested pair of its entries' encodings,
`⟨e₁, ⟨e₂, ⟨…, []⟩⟩⟩`. -/
def encodeLog (codec : MachineCodec spec α) (h : QueryLog spec) : List Bool :=
  h.foldr (fun e acc => pairEncode (codec.encodeEntry e) acc) []

end MachineCodec

/-- The computation of a next-move function `next` with query budget `q`, started from the log
`hist`: a final output stops; a query within budget asks the oracle and continues with the
answer appended to the log; a query when the budget is exhausted gives `timeout`. -/
def buildComp {spec : OracleSpec ι} (next : QueryLog spec → Move spec α) (timeout : α) :
    ℕ → QueryLog spec → OracleComp spec α
  | 0, hist => match next hist with
    | .ret a => .pure a
    | .query _ _ => .pure timeout
  | q + 1, hist => match next hist with
    | .ret a => .pure a
    | .query i x => .query i x (fun y => buildComp next timeout q (hist ++ [⟨i, x, y⟩]))

/-- The computation built with budget `q` makes at most `q` queries, from every log. -/
theorem buildComp_costBoundedBy {spec : OracleSpec ι} (next : QueryLog spec → Move spec α)
    (timeout : α) : ∀ (q : ℕ) (hist : QueryLog spec),
      (buildComp next timeout q hist).CostBoundedBy (fun _ => 1) q
  | 0, hist => by
    unfold buildComp
    cases next hist <;> exact trivial
  | q + 1, hist => by
    unfold buildComp
    cases next hist with
    | ret a => exact trivial
    | query i x => exact ⟨Nat.le_add_left 1 q, fun y => buildComp_costBoundedBy next timeout q _⟩

/-- The oracle computation of the machine `D` at parameter `n`, with coins `r` and query budget
`q`: the machine's next-move function is one activation of `D` on the encoded log.
[PS10, Definition 96.1], generalized to oracle families and arbitrary outputs. -/
def _root_.Complexity.NUPPT.toComp {spec : OracleSpec ι} (D : NUPPT) (codec : MachineCodec spec α)
    (n q : ℕ) (r : D.Coins n) : OracleComp spec α :=
  buildComp (fun hist => codec.decodeMove (D.runAt n (codec.encodeLog hist) r)) codec.timeout q []

/-- A machine's computation makes at most `q` queries. -/
theorem _root_.Complexity.NUPPT.toComp_costBoundedBy {spec : OracleSpec ι} (D : NUPPT)
    (codec : MachineCodec spec α) (n q : ℕ) (r : D.Coins n) :
    (D.toComp codec n q r).CostBoundedBy (fun _ => 1) q :=
  buildComp_costBoundedBy _ _ q []

/-! ### The ch. 2–4 next-query machines are an instance -/

/-- The codec of the ch. 2–4 next-query machines: one oracle on bit strings, a Boolean verdict,
moves decoded by `decodeOracleMove`, entries encoded as in `encodeHist`, and the verdict `false`
when the budget runs out. -/
def singleCodec (ℓ₁ ℓ₂ : ℕ) :
    MachineCodec (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)) Bool where
  decodeMove w := match decodeOracleMove ℓ₁ w with
    | .query x => .query () x
    | .ret b => .ret b
  encodeEntry e := pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)
  timeout := false

/-- The ch. 2–4 history of a one-oracle log: the list of its (query, answer) pairs. -/
def toHist {ℓ₁ ℓ₂ : ℕ} (h : QueryLog (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool))) :
    List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) :=
  h.map fun e => (e.2.1, e.2.2)

/-- The codec's log encoding is the ch. 2–4 history encoding. -/
theorem encodeLog_singleCodec {ℓ₁ ℓ₂ : ℕ}
    (h : QueryLog (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool))) :
    (singleCodec ℓ₁ ℓ₂).encodeLog h = encodeHist (toHist h) := by
  induction h with
  | nil => rfl
  | cons e h ih =>
    simp only [MachineCodec.encodeLog, List.foldr_cons, toHist, List.map_cons, encodeHist] at ih ⊢
    rw [ih]
    rfl

/-- One step of the correspondence: the framework's computation from a log is the translation of
the ch. 2–4 tree from the corresponding history. -/
theorem buildComp_singleCodec {ℓ₁ ℓ₂ : ℕ}
    (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁) :
    ∀ (q : ℕ) (hist : QueryLog (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool))),
      buildComp (fun h => match next (toHist h) with
          | .query x => .query () x
          | .ret b => .ret b) false q hist =
        Bridge.QueryTree.toComp (buildTree next q (toHist hist))
  | 0, hist => by
    unfold buildComp buildTree
    cases next (toHist hist) <;> rfl
  | q + 1, hist => by
    unfold buildComp buildTree
    cases hn : next (toHist hist) with
    | ret b => rfl
    | query x =>
      simp only [Bridge.QueryTree.toComp]
      congr 1
      funext y
      rw [buildComp_singleCodec next q]
      simp [toHist]

/-- **The ch. 2–4 decoder is an instance:** the oracle adversary `D.toOracleAdversary` of a
next-query machine is the translation of its computation under `singleCodec`. So
`OracleEnsemble.Indist` (via `oracleDist`) is a statement about framework computations. -/
theorem toComp_singleCodec (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) (r : D.Coins n) :
    D.toComp (singleCodec ℓ₁ ℓ₂) n q r =
      Bridge.QueryTree.toComp (D.toOracleAdversary n ℓ₁ ℓ₂ q r) := by
  have h := buildComp_singleCodec (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
    (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q []
  have hnext : (fun hist => (singleCodec ℓ₁ ℓ₂).decodeMove
      (D.runAt n ((singleCodec ℓ₁ ℓ₂).encodeLog hist) r)) =
      (fun h => match decodeOracleMove ℓ₁ (D.runAt n (encodeHist (toHist h)) r) with
        | .query x => Move.query () x
        | .ret b => Move.ret b) := by
    funext hist
    rw [encodeLog_singleCodec]
    rfl
  simp only [NUPPT.toComp, NUPPT.toOracleAdversary]
  rw [hnext]
  exact h

end TCSlib.Cryptography.Games
