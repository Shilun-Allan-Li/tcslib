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

/-- Reading a nonempty unary run stops at its following `false`, preserving
the entire suffix. -/
private theorem takeTrues_replicate (k : ℕ) (r : List Bool) :
    takeTrues (List.replicate (k + 1) true ++ false :: r) = (k + 1, false :: r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (let (n, s) := takeTrues (List.replicate (k + 1) true ++ false :: r)
              (n + 1, s)) = _
      rw [ih]

/-- A serialized literal parses correctly with any unconsumed suffix. -/
private theorem parseLit_serializeLit (ℓ : Literal ℕ) (r : List Bool) :
    parseLit (serializeLit ℓ ++ r) = some (ℓ, r) := by
  simp only [serializeLit, List.append_assoc, List.cons_append, List.nil_append,
    parseLit, takeTrues_replicate]

/-- A clause round-trips with any suffix and any fuel at least its serialized
length.

**Proof sketch.** Induct on the literal list. The terminator closes the empty
clause without spending fuel. A literal consumes at least three bits, leaving
the decremented fuel large enough for the tail; apply the literal round trip
and then the induction hypothesis. -/
private theorem parseClause_serializeClause (C : Clause ℕ) (r : List Bool)
    (fuel : ℕ) (hf : (serializeClause C).length ≤ fuel) :
    parseClause fuel (serializeClause C ++ r) = some (C, r) := by
  induction C generalizing fuel with
  | nil => simp only [serializeClause, List.flatMap_nil, List.nil_append,
      List.cons_append, parseClause]
  | cons ℓ C ih =>
      cases fuel with
      | zero =>
          simp only [serializeClause, List.length_append, List.length_cons,
            List.length_nil] at hf
          omega
      | succ fuel =>
          have htail : (serializeClause C).length ≤ fuel := by
            simp only [serializeClause, List.flatMap_cons, List.length_append,
              serializeLit, List.length_replicate, List.length_cons, List.length_nil] at hf ⊢
            omega
          have hx : serializeClause (ℓ :: C) ++ r =
              serializeLit ℓ ++ (serializeClause C ++ r) := by
            simp only [serializeClause, List.flatMap_cons, List.append_assoc]
          rw [hx]
          have hlit := parseLit_serializeLit ℓ (serializeClause C ++ r)
          simp only [serializeLit, List.replicate_succ, List.cons_append] at hlit ⊢
          simp only [parseClause, hlit, ih fuel htail]

/-- A formula round-trips with any suffix and any fuel at least its serialized
length.

**Proof sketch.** Induct on the clause list. The empty formula reads its
terminator. A clause record has its leading marker and a nonempty serialized
body, so the decremented fuel suffices both for the clause body and for the
remaining formula. Thread the same suffix through the two round trips. -/
private theorem parseClauses_serialize (φ : CNF ℕ) (r : List Bool)
    (fuel : ℕ) (hf : (serialize φ).length ≤ fuel) :
    parseClauses fuel (serialize φ ++ r) = some (φ, r) := by
  induction φ generalizing fuel with
  | nil => simp only [serialize, List.flatMap_nil, List.nil_append,
      List.cons_append, parseClauses]
  | cons C φ ih =>
      cases fuel with
      | zero =>
          simp only [serialize, List.length_append, List.length_cons,
            List.length_nil] at hf
          omega
      | succ fuel =>
          have hclause : (serializeClause C).length ≤ fuel := by
            simp only [serialize, List.flatMap_cons, List.length_append,
              List.length_cons, List.length_nil] at hf
            omega
          have htail : (serialize φ).length ≤ fuel := by
            simp only [serialize, List.flatMap_cons, List.length_append,
              List.length_cons, List.length_nil] at hf ⊢
            omega
          have hx : serialize (C :: φ) ++ r =
              true :: (serializeClause C ++ (serialize φ ++ r)) := by
            simp only [serialize, List.flatMap_cons, List.cons_append, List.append_assoc]
          rw [hx]
          simp only [parseClauses, parseClause_serializeClause C _ fuel hclause,
            ih fuel htail]

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
  have h := parseClauses_serialize φ [] (serialize φ).length (Nat.le_refl _)
  simp only [List.append_nil] at h
  simp only [parse, h]

/-- Decoding inverts serialization: `decode` on a serialized formula is the
formula itself.

**Proof sketch.** `Std.Sat.CNF.parse_serialize` and `Option.getD` on a
`some`. -/
theorem decode_serialize (φ : CNF ℕ) : decode (serialize φ) = φ := by
  simp only [decode, parse_serialize, Option.getD_some]

/-- The counted unary run and the returned suffix partition the input length. -/
private theorem takeTrues_length (x : List Bool) :
    (takeTrues x).1 + (takeTrues x).2.length = x.length := by
  induction x with
  | nil => rfl
  | cons b x ih =>
      cases b with
      | false => simp only [takeTrues, Nat.zero_add]
      | true =>
          simp only [takeTrues, List.length_cons]
          omega

/-- A successful literal parse consumes exactly its unary run, terminator,
and polarity bit. -/
private theorem parseLit_length {x r : List Bool} {ℓ : Literal ℕ}
    (h : parseLit x = some (ℓ, r)) : ℓ.1 + 3 + r.length = x.length := by
  have hlen := takeTrues_length x
  unfold parseLit at h
  split at h
  · cases h
  · rename_i k b rest ht
    cases h
    simp only [ht, List.length_cons] at hlen
    omega
  · cases h

/-- On a successful clause parse, the remainder is no longer than the input,
and every variable contribution fits inside the consumed prefix.

**Proof sketch.** Induct on fuel and distinguish the input marker. A closing
marker produces no literals. A literal consumes exactly its index plus three
bits; the induction hypothesis bounds the remaining parse. Add the final
remainder length to each variable contribution to avoid truncated subtraction. -/
private theorem parseClause_bounds {fuel : ℕ} {x r : List Bool} {C : Clause ℕ}
    (h : parseClause fuel x = some (C, r)) :
    r.length ≤ x.length ∧ ∀ ℓ ∈ C, ℓ.1 + 1 + r.length ≤ x.length := by
  induction fuel generalizing x C r with
  | zero =>
      cases x with
      | nil =>
          simp only [parseClause] at h
          cases h
      | cons b s =>
          cases b with
          | false =>
              simp only [parseClause, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              exact ⟨Nat.le_succ _, fun ℓ hℓ => False.elim (List.not_mem_nil hℓ)⟩
          | true =>
              simp only [parseClause] at h
              cases h
  | succ fuel ih =>
      cases x with
      | nil =>
          simp only [parseClause] at h
          cases h
      | cons b s =>
          cases b with
          | false =>
              simp only [parseClause, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              exact ⟨Nat.le_succ _, fun ℓ hℓ => False.elim (List.not_mem_nil hℓ)⟩
          | true =>
              cases hl : parseLit (true :: s) with
              | none =>
                  simp only [parseClause, hl] at h
                  cases h
              | some p =>
                  obtain ⟨lit, t⟩ := p
                  cases hc : parseClause fuel t with
                  | none =>
                      simp only [parseClause, hl, hc] at h
                      cases h
                  | some p =>
                      obtain ⟨D, u⟩ := p
                      simp only [parseClause, hl, hc, Option.some.injEq, Prod.mk.injEq] at h
                      rcases h with ⟨rfl, rfl⟩
                      obtain ⟨hlen, hvars⟩ := ih hc
                      have hcons := parseLit_length hl
                      constructor
                      · omega
                      · intro ℓ hℓ
                        rcases List.mem_cons.mp hℓ with rfl | hℓ
                        · omega
                        · have hv := hvars ℓ hℓ
                          omega

/-- On a successful formula parse, the remainder is no longer than the input,
and every variable contribution fits inside the consumed prefix.

**Proof sketch.** Induct on fuel. A closing marker has no variables. Otherwise,
apply the clause bound to the first clause and the induction hypothesis to
the remaining formula. The final remainder is no longer than either earlier
suffix, so both sets of variable bounds persist when the parses are composed. -/
private theorem parseClauses_bounds {fuel : ℕ} {x r : List Bool} {φ : CNF ℕ}
    (h : parseClauses fuel x = some (φ, r)) :
    r.length ≤ x.length ∧ ∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 + 1 + r.length ≤ x.length := by
  induction fuel generalizing x φ r with
  | zero =>
      cases x with
      | nil =>
          simp only [parseClauses] at h
          cases h
      | cons b s =>
          cases b with
          | false =>
              simp only [parseClauses, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              exact ⟨Nat.le_succ _, fun C hC => False.elim (List.not_mem_nil hC)⟩
          | true =>
              simp only [parseClauses] at h
              cases h
  | succ fuel ih =>
      cases x with
      | nil =>
          simp only [parseClauses] at h
          cases h
      | cons b s =>
          cases b with
          | false =>
              simp only [parseClauses, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              exact ⟨Nat.le_succ _, fun C hC => False.elim (List.not_mem_nil hC)⟩
          | true =>
              cases hc : parseClause fuel s with
              | none =>
                  simp only [parseClauses, hc] at h
                  cases h
              | some p =>
                  obtain ⟨D, t⟩ := p
                  cases ht : parseClauses fuel t with
                  | none =>
                      simp only [parseClauses, hc, ht] at h
                      cases h
                  | some p =>
                      obtain ⟨ψ, u⟩ := p
                      simp only [parseClauses, hc, ht, Option.some.injEq, Prod.mk.injEq] at h
                      rcases h with ⟨rfl, rfl⟩
                      obtain ⟨hclen, hcvars⟩ := parseClause_bounds hc
                      obtain ⟨htlen, htvars⟩ := ih ht
                      simp only [List.length_cons]
                      constructor
                      · omega
                      · intro C hC ℓ hℓ
                        rcases List.mem_cons.mp hC with rfl | hC
                        · have hv := hcvars ℓ hℓ
                          omega
                        · have hv := htvars C hC ℓ hℓ
                          omega

/-- A uniform bound on literal contributions bounds the formula's maximum
variable index plus one. -/
private theorem numVars_le_of_literal_bounds (φ : CNF ℕ) (n : ℕ)
    (h : ∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 + 1 ≤ n) : φ.numVars ≤ n := by
  have fold_bound : ∀ s : List ℕ, (∀ k ∈ s, k ≤ n) → s.foldr max 0 ≤ n := by
    intro s hs
    induction s with
    | nil => exact Nat.zero_le _
    | cons k s ih =>
        exact Nat.max_le.mpr ⟨hs k List.mem_cons_self,
          ih (fun j hj => hs j (List.mem_cons_of_mem k hj))⟩
  unfold numVars
  apply fold_bound
  intro k hk
  obtain ⟨C, hC, hk⟩ := List.mem_flatMap.mp hk
  obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hk
  exact h C hC ℓ hℓ

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
  unfold decode parse
  cases hp : parseClauses x.length x with
  | none => exact Nat.zero_le _
  | some p =>
      obtain ⟨φ, r⟩ := p
      cases r with
      | nil =>
          change φ.numVars ≤ x.length
          apply numVars_le_of_literal_bounds
          intro C hC ℓ hℓ
          simpa only [List.length_nil, Nat.add_zero] using
            (parseClauses_bounds hp).2 C hC ℓ hℓ
      | cons b r => exact Nat.zero_le _

end Std.Sat.CNF
