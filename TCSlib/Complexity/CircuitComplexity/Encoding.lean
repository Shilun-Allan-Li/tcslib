/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Computability.Encoding
import Mathlib.Computability.Language
import TCSlib.Complexity.CircuitComplexity.CircuitSat

/-!
# Encoding circuits, CKT-SAT as a language, and the clause count of Lemma 6.11

## Main definitions

* `ACP.encodeCircuit`, `ACP.readCircuit` — a prefix serialisation of
  `BoolCircuit.Circuit` into `List Bool`, and the parser that reads it back.
* `ACP.encodeSigma`, `ACP.decodeSigma`, `ACP.circuitEncoding` — the same for an
  arity-tagged circuit, packaged as a `Computability.FinEncoding`.
* `ACP.cktSatLang` — CKT-SAT as a `Language Bool`.  [AB09, Def 6.9]

## Main results

* `ACP.decodeSigma_encodeSigma`, `ACP.encodeSigma_of_decodeSigma` — the encoding
  round-trips, and only canonical strings decode.
* `ACP.mem_cktSatLang_iff`, `ACP.mem_cktSatLang_iff_exists` — `cktSatLang` is
  exactly the image of `BoolCircuit.CktSat` under the encoding.
* `ACP.size_le_length_encodeSigma` — a circuit is never larger than its encoding
  is long, so a bound in the size is a bound in the input length.
* `ACP.length_to3SAT_toCNF_le` — the reduction of [AB09, Lem 6.11] outputs at
  most `13 * |encoding|` 3-clauses.

## Divergences from Arora–Barak §6.1.2 and §6.2

**No `≤p` claim is made or supported here.** `≤p` is polynomial-*time*
reducibility; TCSlib has no machine model, so the cost of computing the
reduction is bounded nowhere, and the time half of [AB09, Lem 6.11] remains
unformalized, as `CircuitSat.lean` already records. What is added is a bound on
the reduction's *output*, and only on its number of 3-clauses: the output's
variable type `SATTo3SAT.AuxVar (BoolCircuit.CktVar n)` is infinite (`CktVar n`
is indexed by all of `Circuit n`), so no encoding of the output formula exists
here and its bit length is not bounded.

AB's concrete representation ([AB09, p. 112]) is the `S × S` adjacency matrix of
a size-`S` circuit's DAG plus an array of `S` gate labels, vertices identified
with `[S]`.  `BoolCircuit.Circuit` is a tree, so that representation is not
available: there is no vertex numbering to index a matrix by, and the accessors
`SIZE`/`TYPE`/`EDGE` are not defined here.  AB offers the matrix as "a concrete
way", in a remark that [AB09, Def 6.14] "is robust to variations in how we
represent circuits using strings" — a robustness AB asserts rather than proves,
and which nothing below uses.  This file gives the concrete way for a tree: a
tag bit saying leaf or gate, then either the leaf's sign and variable index or
the gate's connective and its children, the children delimited by a
continue/stop bit.  Natural numbers are written in unary, which inflates the
encoding by a polynomial factor — `O(n)` rather than `O(log n)` bits for an index
below `n` — and only upwards.  Every bound below is an upper bound in the
encoding's length, so the inflation cannot weaken one, and being polynomial it
cannot break a later polynomial-time claim either.

`decodeSigma` parses and then checks that the parse re-encodes to its input, so
non-canonical strings decode to `none` and are simply absent from `cktSatLang`.

`Computability.FinEncoding` is used rather than a new class: it is exactly an
encode/decode pair over a finite alphabet, and it is the interface the
Turing-machine track works against.  `Encodable`/`Denumerable` were not used
because they encode into `ℕ`, which supplies no string and so no input length
for a bound to be stated in.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace ACP

open BoolCircuit SATTo3SAT

/-! ## Serialising a circuit -/

/-- `k` in unary: `k` `true`s terminated by a `false`. -/
private def unaryBits (k : ℕ) : List Bool := List.replicate k true ++ [false]

/-- Read one `unaryBits` block off the front of a bit string. -/
private def readUnary : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (readUnary rest).map fun p => (p.1 + 1, p.2)

/-- Reading back a `unaryBits` block returns its number and the untouched remainder. -/
private theorem readUnary_unaryBits (k : ℕ) (rest : List Bool) :
    readUnary (unaryBits k ++ rest) = some (k, rest) := by
  induction k with
  | zero => simp [unaryBits, readUnary]
  | succ k ih => simpa [unaryBits, readUnary, List.replicate_succ] using ih

/-- A circuit as a bit string: a leaf is `false`, its sign, its index in unary;
a gate is `true`, its connective, then its children, each prefixed by `true` and
the list terminated by `false`. -/
def encodeCircuit {n : ℕ} : Circuit n → List Bool
  | .lit l => false :: l.sign :: unaryBits l.idx.val
  | .node b cs => (true :: b :: (cs.flatMap fun c => true :: encodeCircuit c)) ++ [false]

/-- The children block of a gate's encoding. -/
def encodeChildren {n : ℕ} (cs : List (Circuit n)) : List Bool :=
  (cs.flatMap fun c => true :: encodeCircuit c) ++ [false]

/-- A gate's encoding is its tag bit, its connective bit, then its children block. -/
theorem encodeCircuit_node {n : ℕ} (b : Bool) (cs : List (Circuit n)) :
    encodeCircuit (.node b cs) = true :: b :: encodeChildren cs := by
  simp [encodeCircuit, encodeChildren]

/-- The empty children block is the lone stop bit. -/
theorem encodeChildren_nil {n : ℕ} : encodeChildren ([] : List (Circuit n)) = [false] := by
  simp [encodeChildren]

/-- A non-empty children block is a continue bit, the head's encoding, then the
block for the tail. -/
theorem encodeChildren_cons {n : ℕ} (d : Circuit n) (ds : List (Circuit n)) :
    encodeChildren (d :: ds) = true :: (encodeCircuit d ++ encodeChildren ds) := by
  simp [encodeChildren, List.append_assoc]

/-! ## Parsing it back

Recursive descent, with a fuel argument in place of a termination measure; the
callers supply the input's length, which always suffices. -/

mutual

/-- Read one circuit off the front of a bit string, returning the remainder. -/
def readCircuit (n : ℕ) : ℕ → List Bool → Option (Circuit n × List Bool)
  | 0, _ => none
  | fuel + 1, bs =>
      match bs with
      | false :: s :: rest =>
          match readUnary rest with
          | none => none
          | some (i, r) => if h : i < n then some (.lit ⟨⟨i, h⟩, s⟩, r) else none
      | true :: b :: rest =>
          match readChildren n fuel rest with
          | none => none
          | some (cs, r) => some (.node b cs, r)
      | _ => none

/-- Read a gate's children block off the front of a bit string. -/
def readChildren (n : ℕ) : ℕ → List Bool → Option (List (Circuit n) × List Bool)
  | 0, _ => none
  | fuel + 1, bs =>
      match bs with
      | false :: rest => some ([], rest)
      | true :: rest =>
          match readCircuit n fuel rest with
          | none => none
          | some (c, r) =>
              match readChildren n fuel r with
              | none => none
              | some (cs, r') => some (c :: cs, r')
      | _ => none

end

/-- Given that each child parses back, so does a children block.

**Proof sketch.** Induction on the list of children.  The empty block is the
single stop bit, which the parser consumes outright.  A non-empty block is a
continue bit, the head child's encoding and the block for the tail, in that
order; one unit of fuel pays for the continue bit, the hypothesis for the head
returns the tail's block as its remainder, and the induction hypothesis consumes
that.  Fuel suffices at each step because the block's length is the sum of the
two sub-lengths plus one. -/
theorem readChildren_encodeChildren {n : ℕ} (ds : List (Circuit n))
    (h : ∀ d ∈ ds, ∀ (fuel : ℕ) (rest : List Bool), (encodeCircuit d).length ≤ fuel →
      readCircuit n fuel (encodeCircuit d ++ rest) = some (d, rest)) :
    ∀ (fuel : ℕ) (rest : List Bool), (encodeChildren ds).length ≤ fuel →
      readChildren n fuel (encodeChildren ds ++ rest) = some (ds, rest) := by
  induction ds with
  | nil =>
      intro fuel rest hf
      rw [encodeChildren_nil] at hf ⊢
      match fuel with
      | 0 => simp at hf
      | f + 1 => simp [readChildren]
  | cons d ds ih =>
      intro fuel rest hf
      have hd := h d List.mem_cons_self
      have ih' := ih fun e he => h e (List.mem_cons_of_mem _ he)
      rw [encodeChildren_cons] at hf ⊢
      simp only [List.length_cons, List.length_append] at hf
      match fuel with
      | 0 => simp at hf
      | f + 1 =>
          simp only [List.cons_append, readChildren, List.append_assoc]
          simp only [hd f (encodeChildren ds ++ rest) (by omega), ih' f rest (by omega)]

/-- The parser recovers any encoded circuit, given fuel at least the encoding's length.

**Proof sketch.** Structural induction on the circuit.  A leaf is a tag bit, a
sign bit and a unary index, which the unary reader returns together with the
untouched remainder; the index is in range because it came from a `Fin n`.  A
gate is a tag bit, a connective bit and a children block; the children block is
handled by the previous lemma, whose hypothesis is exactly what the induction
supplies for the children. -/
theorem readCircuit_encodeCircuit {n : ℕ} (C : Circuit n) :
    ∀ (fuel : ℕ) (rest : List Bool), (encodeCircuit C).length ≤ fuel →
      readCircuit n fuel (encodeCircuit C ++ rest) = some (C, rest) := by
  induction C using Circuit.ind with
  | hlit l =>
      intro fuel rest hf
      match fuel with
      | 0 => simp [encodeCircuit] at hf
      | f + 1 =>
          simp only [encodeCircuit, List.cons_append, readCircuit]
          rw [readUnary_unaryBits]
          simp
  | hnode b cs ih =>
      intro fuel rest hf
      rw [encodeCircuit_node] at hf ⊢
      simp only [List.length_cons] at hf
      match fuel with
      | 0 => simp at hf
      | f + 1 =>
          simp only [List.cons_append, readCircuit]
          rw [readChildren_encodeChildren cs ih f rest (by omega)]

/-! ## The encoding -/

/-- An arity-tagged circuit as a bit string: the arity in unary, then the circuit. -/
def encodeSigma : ((n : ℕ) × Circuit n) → List Bool
  | ⟨n, C⟩ => unaryBits n ++ encodeCircuit C

/-- Parse a bit string as an arity-tagged circuit, accepting only strings that
re-encode to themselves. -/
def decodeSigma (bs : List Bool) : Option ((n : ℕ) × Circuit n) :=
  match readUnary bs with
  | none => none
  | some (n, r) =>
      match readCircuit n r.length r with
      | some (C, []) => if encodeSigma ⟨n, C⟩ = bs then some ⟨n, C⟩ else none
      | _ => none

/-- Every encoded circuit decodes back to itself. -/
theorem decodeSigma_encodeSigma (C : (n : ℕ) × Circuit n) :
    decodeSigma (encodeSigma C) = some C := by
  obtain ⟨n, C⟩ := C
  simp only [decodeSigma, encodeSigma, readUnary_unaryBits]
  rw [show readCircuit n (encodeCircuit C).length (encodeCircuit C) = some (C, []) by
    simpa using readCircuit_encodeCircuit C (encodeCircuit C).length [] le_rfl]
  simp

/-- Only the encoding of `C` decodes to `C`. -/
theorem encodeSigma_of_decodeSigma {bs : List Bool} {C : (n : ℕ) × Circuit n}
    (h : decodeSigma bs = some C) : encodeSigma C = bs := by
  unfold decodeSigma at h
  split at h
  · exact absurd h (by simp)
  · rename_i n r hr
    split at h
    · rename_i C' hC'
      split at h
      · rename_i hEq
        obtain rfl := Option.some.inj h
        exact hEq
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- The circuit encoding, as a `Computability.FinEncoding` over the alphabet `Bool`. -/
def circuitEncoding : Computability.FinEncoding ((n : ℕ) × Circuit n) where
  Γ := Bool
  encode := encodeSigma
  decode := decodeSigma
  decode_encode := decodeSigma_encodeSigma
  ΓFin := inferInstance

/-- The packaged encoding's `encode` field is `encodeSigma`. -/
theorem circuitEncoding_encode : circuitEncoding.encode = encodeSigma := rfl

/-- The packaged encoding's `decode` field is `decodeSigma`. -/
theorem circuitEncoding_decode : circuitEncoding.decode = decodeSigma := rfl

/-! ## CKT-SAT as a language -/

/-- CKT-SAT: the bit strings encoding a satisfiable circuit.  [AB09, Def 6.9] -/
def cktSatLang : Language Bool :=
  {w | ∃ C, decodeSigma w = some C ∧ C ∈ CktSat}

/-- `cktSatLang` and `BoolCircuit.CktSat` agree under the encoding. -/
theorem mem_cktSatLang_iff (C : (n : ℕ) × Circuit n) :
    encodeSigma C ∈ cktSatLang ↔ C ∈ CktSat := by
  constructor
  · rintro ⟨D, hD, hmem⟩
    rw [decodeSigma_encodeSigma C] at hD
    obtain rfl : C = D := Option.some.inj hD
    exact hmem
  · exact fun h => ⟨C, decodeSigma_encodeSigma C, h⟩

/-- `cktSatLang` is exactly the image of `CktSat` under the encoding. -/
theorem mem_cktSatLang_iff_exists (w : List Bool) :
    w ∈ cktSatLang ↔ ∃ C ∈ CktSat, encodeSigma C = w := by
  constructor
  · rintro ⟨C, hC, hmem⟩
    exact ⟨C, hmem, encodeSigma_of_decodeSigma hC⟩
  · rintro ⟨C, hmem, rfl⟩
    exact (mem_cktSatLang_iff C).mpr hmem

/-! Degenerate cases: zero inputs, the empty `AND` and the empty `OR`, a single
literal, and a string that encodes nothing. -/

example : encodeSigma ⟨0, .node true []⟩ = [false, true, true, false] := by
  simp [encodeSigma, encodeCircuit, unaryBits]

example : decodeSigma [false, true, true, false] = some ⟨0, .node true []⟩ := by
  simp [decodeSigma, readUnary, readCircuit, readChildren, encodeSigma, encodeCircuit, unaryBits]

example : encodeSigma ⟨0, .node true []⟩ ∈ cktSatLang :=
  (mem_cktSatLang_iff _).mpr ⟨finZeroElim, by simp [Circuit.eval]⟩

example : encodeSigma ⟨0, .node false []⟩ ∉ cktSatLang := by
  rw [mem_cktSatLang_iff]
  rintro ⟨u, hu⟩
  simp [Circuit.eval] at hu

example : encodeSigma ⟨1, .lit ⟨0, true⟩⟩ ∈ cktSatLang :=
  (mem_cktSatLang_iff _).mpr ⟨fun _ => true, by simp [Circuit.eval]⟩

example : ([] : List Bool) ∉ cktSatLang := by
  rintro ⟨C, hC, -⟩
  simp [decodeSigma, readUnary] at hC

/-! ## Clause count of the reduction to 3SAT -/

/-- No circuit is larger than its encoding is long.

**Proof sketch.** Structural induction.  A leaf has size one against an encoding
of at least three bits.  A gate's size is one plus the total size of its
children, and its encoding is two bits plus the children block; a side induction
on the list of children shows the children's total size is at most the block's
length, since each child contributes its own encoding and a continue bit. -/
theorem size_le_length_encodeCircuit {n : ℕ} (C : Circuit n) :
    C.size ≤ (encodeCircuit C).length := by
  induction C using Circuit.ind with
  | hlit l => simp [encodeCircuit, Circuit.size, unaryBits]
  | hnode b cs ih =>
      have hlist : ∀ ds : List (Circuit n), (∀ d ∈ ds, d.size ≤ (encodeCircuit d).length) →
          ds.foldr (fun d acc => d.size + acc) 0 ≤ (encodeChildren ds).length := by
        intro ds hds
        induction ds with
        | nil => simp [encodeChildren_nil]
        | cons d ds ihd =>
            have h1 := hds d List.mem_cons_self
            have h2 := ihd fun e he => hds e (List.mem_cons_of_mem _ he)
            rw [encodeChildren_cons]
            simp only [List.foldr_cons, List.length_cons, List.length_append]
            omega
      have hsum := hlist cs ih
      rw [encodeCircuit_node]
      simp only [Circuit.size, List.length_cons]
      omega

/-- An arity-tagged circuit's size never exceeds the length of its encoding. -/
theorem size_le_length_encodeSigma (C : (n : ℕ) × Circuit n) :
    C.2.size ≤ (encodeSigma C).length := by
  obtain ⟨n, C⟩ := C
  have h := size_le_length_encodeCircuit C
  simp only [encodeSigma, List.length_append, unaryBits, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

/-- One gate's clauses use `3` literal occurrences per child, plus one. -/
theorem gateClauses_flatten_length {n : ℕ} (b : Bool) (cs : List (Circuit n)) :
    (gateClauses b cs).flatten.length = 3 * cs.length + 1 := by
  have key : ∀ (x : Literal (CktVar n)) (g : Circuit n → Literal (CktVar n))
      (ds : List (Circuit n)), (ds.map fun c => [x, g c]).flatten.length = 2 * ds.length := by
    intro x g ds
    induction ds with
    | nil => simp
    | cons d ds ih => simp [ih]; omega
  cases b <;> simp [gateClauses, key] <;> omega

/-- The gate clauses of `C` use fewer than `7 * C.size` literal occurrences.

**Proof sketch.** Structural induction, in the same shape as
`BoolCircuit.Circuit.tseitin_length_lt`.  A leaf contributes four occurrences
against a size of one, and `7 - 3` is four.  At a gate the statement is
strengthened by three units of slack so that it survives the passage to the
children: a side induction on the list of children shows their occurrences,
*plus three per child*, still fit inside seven times their total size.  The
gate's own clauses cost three occurrences per child plus one, so those three per
child are exactly what the side induction set aside, and the gate's node itself
contributes the remaining seven units. -/
theorem tseitin_flatten_length_le {n : ℕ} (C : Circuit n) :
    C.tseitin.flatten.length + 3 ≤ 7 * C.size := by
  induction C using Circuit.ind with
  | hlit l => simp [Circuit.tseitin, Circuit.size]
  | hnode b cs ih =>
      have hlist : ∀ ds : List (Circuit n),
          (∀ d ∈ ds, d.tseitin.flatten.length + 3 ≤ 7 * d.size) →
          (ds.flatMap fun d => d.tseitin).flatten.length + 3 * ds.length ≤
            7 * ds.foldr (fun d acc => d.size + acc) 0 := by
        intro ds hds
        induction ds with
        | nil => simp
        | cons d ds ihd =>
            have h1 := hds d List.mem_cons_self
            have h2 := ihd fun e he => hds e (List.mem_cons_of_mem _ he)
            simp only [List.flatMap_cons, List.flatten_append, List.length_append,
              List.length_cons, List.foldr_cons]
            omega
      have hsum := hlist cs ih
      have hg := gateClauses_flatten_length b cs
      simp only [Circuit.tseitin, List.flatten_append, List.length_append, Circuit.size, hg]
      omega

/-- The CNF the reduction builds uses at most `7 * C.size` literal occurrences. -/
theorem toCNF_flatten_length_le {n : ℕ} (C : Circuit n) :
    C.toCNF.flatten.length ≤ 7 * C.size := by
  have h := tseitin_flatten_length_le C
  simp only [Circuit.toCNF, List.flatten_cons, List.length_append, List.length_cons,
    List.length_nil]
  omega

/-- The 3-CNF that [AB09, Lem 6.11] produces from a circuit has at most `13`
clauses per bit of the encoded circuit.

This is the clause-count half of the lemma and nothing more: it says how many
3-clauses come out, not how long they take to build, so it is not a `≤p`
statement.  AB gives no constant; `13` is this formalization's, read off the
clause counts above. -/
theorem length_to3SAT_toCNF_le (C : (n : ℕ) × Circuit n) :
    (to3SAT C.2.toCNF).length ≤ 13 * (encodeSigma C).length := by
  have h1 := SATTo3SAT.length_to3SAT_le C.2.toCNF
  have h2 := toCNF_flatten_length_le C.2
  have h3 := C.2.toCNF_length_le
  have h4 := size_le_length_encodeSigma C
  omega

end ACP
