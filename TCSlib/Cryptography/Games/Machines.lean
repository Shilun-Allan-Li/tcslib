/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Complexity.Randomized.PPT

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
decode into moves, and how a query-log entry encodes as a string. It needs only the machine model
and the framework, so the asymptotic layer can build on it. The ch. 2–4 layer's
`NUPPT.toOracleAdversary` (one oracle, a Boolean verdict) is the instance with the codec built
from its own `decodeOracleMove` and `encodeHist` (`TCSlib.Cryptography.Games.Bridges.Machines`).

The efficiency counterpart (a reduction written as an implementation of polynomial-time
computable handlers, run on a machine, is again a machine's computation) is the S2b efficiency
result, stated in a later module.

## Main definitions

* `Games.Move spec α`: a query to an oracle of `spec`, or a final output in `α`.
* `Games.MachineCodec spec α`: decoding of moves and encoding of log entries.
* `Games.buildComp next timeout q hist`: the computation of a next-move function with budget `q`.
* `Complexity.NUPPT.toComp D codec n q r`: the computation of the machine `D` at parameter `n`
  with coins `r`.

## Main results

* `Games.buildComp_costBoundedBy`, `NUPPT.toComp_costBoundedBy`: the computation makes at most `q`
  queries.

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

end TCSlib.Cryptography.Games
