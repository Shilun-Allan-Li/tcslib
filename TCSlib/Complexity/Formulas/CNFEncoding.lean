/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.CNF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary serialization of CNF formulas

The languages `SAT` and `3SAT` are sets of **binary strings** ([AB09, §2.3.1]),
so formulas need a serialization, a parser, and — per [AB09, footnote 3] — a
totalization mapping non-well-formed strings to "some fixed formula". This module
supplies all three, together with the statements that tie them together: the
parse/serialize round trip and the variable-count bound that certificate-length
formulas rely on.

## Design and deviations from [AB09]

* **[AB09] fixes no concrete scheme** (footnote 3 explicitly waves the issue);
  any polynomially bounded, machine-parsable scheme is faithful. Ours is chosen
  for **parser-machine simplicity** and is the phase-3 serialization design
  question's provisional answer (see the plan's decision log):
  - a **literal** `(v, b)` is `v + 1` `true`s, then `false`, then the bit `b` —
    variable indices in **unary**, so the parsing machine counts a run instead
    of doing binary arithmetic;
  - a **clause** is its literals concatenated, then `false` (a clause-start
    position reading `false` means the clause is over — unambiguous, since
    every literal starts with `true`);
  - a **formula** is each clause prefixed by `true`, concatenated, then `false`
    (a formula-level position reading `true` announces another clause, `false`
    ends the formula).
  The grammar is LL(1): at every position the next bit alone determines the
  production. The empty formula is `[false]`; the empty clause is
  `[true, false]`.
* **Unary indices cost only a polynomial factor**: a literal on variable `v`
  occupies `v + 3` bits, so a serialized formula has length at least the sum of
  its `v + 1`-runs — which is what makes `numVars_decode_le` (below) true with
  the plain bound `|x|` — and at most polynomially more than any binary-index
  scheme on the formulas the campaign produces (the Cook-Levin tableau formula
  has polynomially many variables, so its unary serialization stays
  polynomial). Every downstream consumer is polynomial-time, so the choice is
  immaterial to every stated class-membership or hardness result.
* **The parser is fuel-indexed**: `parseClause`/`parseClauses` recurse on an
  explicit fuel argument (structural recursion, no termination proof
  obligations), and `parse` supplies fuel `x.length` — adequate because every
  production consumes at least one input bit before recursing, which is part of
  the round-trip statement's burden, not an axiom.
* **Exact consumption**: `parse` succeeds only when the grammar consumes the
  whole string; trailing garbage makes a string non-well-formed.
* **The fallback is the empty formula** `[]` — trivially satisfiable, a
  tautology, and of width `0`. [AB09, footnote 3] maps non-well-formed strings
  to "some fixed formula" and notes the choice is immaterial; consequences of
  this particular choice (every non-well-formed string lies in `SAT` and
  `3SAT`) are recorded where the languages are defined.

## Main definitions

* `Std.Sat.CNF.serialize` (with `serializeLit`, `serializeClause`) — the
  encoding.
* `Std.Sat.CNF.parse` (with `takeTrues`, `parseLit`, `parseClause`,
  `parseClauses`) — the exact-consumption parser.
* `Std.Sat.CNF.fallback`, `Std.Sat.CNF.decode` — the [AB09, footnote 3]
  totalization.

## Main results

* `Std.Sat.CNF.parse_serialize`, `Std.Sat.CNF.decode_serialize` — the round
  trip: serialized formulas are well-formed and decode to themselves.
* `Std.Sat.CNF.numVars_decode_le` — a decoded formula mentions at most `|x|`
  variables; the bound certificate-length formulas are budgeted against.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.3.1 with footnote 3, p. 45.)
-/

namespace Std.Sat.CNF

/-- Serialize one literal `(v, b)`: the variable index in unary (`v + 1` `true`s
— nonempty even for `v = 0`), the run terminator `false`, then the polarity bit
`b` verbatim. -/
def serializeLit (ℓ : Literal ℕ) : List Bool :=
  List.replicate (ℓ.1 + 1) true ++ [false, ℓ.2]

/-- Serialize one clause: its literals concatenated, closed by `false`. The
terminator is unambiguous because every literal begins with `true`. -/
def serializeClause (C : Clause ℕ) : List Bool :=
  C.flatMap serializeLit ++ [false]

/-- Serialize a formula: every clause prefixed by `true`, concatenated, closed
by `false`. At any formula-level position, `true` announces another clause and
`false` ends the formula; the empty formula is `[false]`. -/
def serialize (φ : CNF ℕ) : List Bool :=
  (φ.flatMap fun C => true :: serializeClause C) ++ [false]

/-- Split off the leading run of `true`s: `takeTrues x = (k, rest)` where `x`
begins with exactly `k` `true`s and `rest` is the remainder (which is empty or
begins with `false`). -/
def takeTrues : List Bool → ℕ × List Bool
  | true :: r => let (k, rest) := takeTrues r; (k + 1, rest)
  | r => (0, r)

/-- Parse one literal from the front: a nonempty run of `k + 1` `true`s, the
terminator `false`, and a polarity bit yield the literal `(k, ·)` and the
unconsumed remainder; anything else (no leading `true`, or the string ending
inside the literal) fails. -/
def parseLit (x : List Bool) : Option (Literal ℕ × List Bool) :=
  match takeTrues x with
  | (0, _) => none
  | (k + 1, false :: b :: rest) => some ((k, b), rest)
  | _ => none

/-- Parse one clause body with explicit fuel: a leading `false` closes the
clause; a leading `true` parses one literal and recurses. Exhausted fuel or an
exhausted string inside a clause fails. `Std.Sat.CNF.parse` supplies fuel
`x.length`, adequate because every literal consumes at least three bits. -/
def parseClause : ℕ → List Bool → Option (Clause ℕ × List Bool)
  | _, false :: rest => some ([], rest)
  | fuel + 1, x@(true :: _) =>
      match parseLit x with
      | some (ℓ, rest) =>
          match parseClause fuel rest with
          | some (C, rest') => some (ℓ :: C, rest')
          | none => none
      | none => none
  | _, _ => none

/-- Parse a clause list with explicit fuel: a leading `false` ends the formula;
a leading `true` parses one clause and recurses. -/
def parseClauses : ℕ → List Bool → Option (CNF ℕ × List Bool)
  | _, false :: rest => some ([], rest)
  | fuel + 1, true :: rest =>
      match parseClause fuel rest with
      | some (C, rest') =>
          match parseClauses fuel rest' with
          | some (φ, rest'') => some (C :: φ, rest'')
          | none => none
      | none => none
  | _, _ => none

/-- Parse a whole string as a formula, requiring **exact consumption**: the
grammar must account for every bit, and trailing garbage fails the parse.
Fuel `x.length` is adequate because every production consumes at least one bit
before recursing (part of the round-trip statement's burden). -/
def parse (x : List Bool) : Option (CNF ℕ) :=
  match parseClauses x.length x with
  | some (φ, []) => some φ
  | _ => none

/-- The fixed fallback formula of [AB09, footnote 3]: the empty CNF — trivially
satisfiable, a tautology, and of width `0`. -/
def fallback : CNF ℕ := []

/-- Total decoding: parse, and map non-well-formed strings to the fixed
`Std.Sat.CNF.fallback` ([AB09, footnote 3] — "such strings represent some fixed
formula"; the `Turing.MachineCode` decode-totality convention is the in-repo
precedent). -/
def decode (x : List Bool) : CNF ℕ :=
  (parse x).getD fallback

/-- **The round trip**: serialized formulas parse back to themselves (with the
whole string consumed).

**Proof sketch.** Strengthen to suffix-carrying forms and induct.
(i) `takeTrues (List.replicate (k+1) true ++ false :: r) = (k+1, false :: r)`
by induction on `k`, so `parseLit (serializeLit ℓ ++ r) = some (ℓ, r)`.
(ii) For every clause `C` and suffix `r`, and any fuel at least
`(serializeClause C).length`,
`parseClause fuel (serializeClause C ++ r) = some (C, r)`: induction on `C`,
the nil case reading the closing `false`, the cons case chaining (i) and the
induction hypothesis — each literal consumes at least three bits, so the fuel
decrement stays adequate. (iii) The analogous statement for `parseClauses` over
the clause list, each clause consuming at least two bits. (iv) Instantiate at
the empty suffix: fuel `(serialize φ).length` suffices, the final `false` closes
the formula, and the remainder is exactly `[]`, so `parse` accepts. -/
theorem parse_serialize (φ : CNF ℕ) : parse (serialize φ) = some φ := by
  sorry

/-- Decoding inverts serialization: `decode` on a serialized formula is the
formula itself.

**Proof sketch.** `Std.Sat.CNF.parse_serialize` and `Option.getD` on a
`some`. -/
theorem decode_serialize (φ : CNF ℕ) : decode (serialize φ) = φ := by
  sorry

/-- **A decoded formula mentions at most `|x|` variables**: for every string
`x`, `(decode x).numVars ≤ x.length`. This is the bound that lets the `SAT`
certificate length be the explicit formula `(n + 1)` bits — an assignment
certificate never needs more bits than the input is long.

**Proof sketch.** For the fallback (parse failure), `numVars [] = 0`. For a
successful parse, strengthen over the parsing functions: whenever
`parseLit`/`parseClause`/`parseClauses` succeeds on a string `y` returning a
remainder `r`, the consumed prefix has length `y.length - r.length`, and every
literal `(k, b)` produced consumed its own `k + 1` `true`s within that prefix —
so `k + 1 ≤ y.length`. Every mentioned variable of the parsed formula therefore
satisfies `v + 1 ≤ x.length`, and the `foldr max` defining
`Std.Sat.CNF.numVars` is bounded by `x.length` (each contribution is). -/
theorem numVars_decode_le (x : List Bool) : (decode x).numVars ≤ x.length := by
  sorry

end Std.Sat.CNF
