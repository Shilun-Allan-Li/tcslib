/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-code parser

The parser/decoder layer for the fixed serialization of coded machines
(`Turing.CodeTM.serialize`): field readers for the exact serialization grammar of
the phase-3 re-audit (Argument A), the total decoder `Turing.codeDecode` with its
padded round-trip law, parser soundness, and the erased suffix scanner
`Turing.codeScan` behind the canonizer target `Turing.codeCanonical`. This module
was split out mechanically from `TCSlib.Complexity.TuringMachine.Encoding` at the
epoch-3→4 merge; its content is the epoch-3 fill, batch A.

## Main definitions

* `Turing.codeDecode` — total decoding: every malformed string denotes the fixed
  fallback machine.
* `Turing.codeScan` / `Turing.codeCanonical` — the erased suffix scanner and the
  canonical-serialization function it induces.

## Main results

* `Turing.codeDecode_serialize_pad` — the decoder recovers a serialized machine
  under arbitrary `true`-padding.
* `Turing.codeCanonical_eq` — the scanner-based canonizer computes exactly
  `fun xs => (codeDecode xs).serialize`.
* The format-independent field-reader layer — the readers `Turing.codeReadFin`,
  `codeReadSign`, `codeReadOutput`, `codeReadWrite`, `codeReadState`,
  `codeReadSymbols`, `codeReadVec`; their exact prefix inverses (`_append`),
  soundness (`_sound`) and suffix-erasure (`codeErase*`) laws; `codeBitsNat_bits`
  and `codeFlatMap_length` — for reuse by other machine-code formats.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, pp. 19-20.)

## Item-8 appendix

The record, table-format and total-decoder layer now lives in `CodeFormat`.
This module retains the shared field readers, erasure laws and fixed one-tape skipper.
-/

namespace Turing

/-- Read a unary natural, stopping at its first false bit. -/
def codeReadUnary : List Bool → Option (ℕ × List Bool)
  | false :: xs => some (0, xs)
  | true :: xs => (codeReadUnary xs).map fun p => (p.1 + 1, p.2)
  | [] => none

/-- The unary reader leaves an arbitrary suffix untouched. -/
lemma codeReadUnary_append (n : ℕ) (xs : List Bool) :
    codeReadUnary (List.replicate n true ++ false :: xs) = some (n, xs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [List.replicate_succ, codeReadUnary] using
      congrArg (Option.map fun p : ℕ × List Bool => (p.1 + 1, p.2)) ih

/-- A unary index is accepted only when it belongs to the declared state space. -/
def codeReadFin (n : ℕ) (xs : List Bool) : Option (Fin n × List Bool) := do
  let (i, rest) ← codeReadUnary xs
  if h : i < n then some (⟨i, h⟩, rest) else none

/-- Decode the fixed dictionary for a head movement. -/
def codeReadSign : List Bool → Option (SignType × List Bool)
  | true :: true :: xs => some (.neg, xs)
  | false :: false :: xs => some (.zero, xs)
  | true :: false :: xs => some (.pos, xs)
  | _ => none

/-- Decode the fixed dictionary for an optional output bit. -/
def codeReadOutput : List Bool → Option (Option Bool × List Bool)
  | false :: false :: xs => some (none, xs)
  | true :: false :: xs => some (some false, xs)
  | true :: true :: xs => some (some true, xs)
  | _ => none

/-- Decode the fixed dictionary for an optional work-tape write. -/
def codeReadWrite : List Bool → Option (Option (Option Bool) × List Bool)
  | false :: false :: xs => some (none, xs)
  | false :: true :: xs => some (some none, xs)
  | true :: false :: xs => some (some (some false), xs)
  | true :: true :: xs => some (some (some true), xs)
  | _ => none

/-- Read the halt tag or a range-checked live successor state. -/
def codeReadState (n : ℕ) : List Bool → Option (Option (Fin n) × List Bool)
  | false :: xs => some (none, xs)
  | true :: xs => (codeReadFin n xs).map fun p => (some p.1, p.2)
  | [] => none

/-- Read one entry for each tape symbol, in blank/false/true order. -/
def codeReadSymbols {A : Type} (read : List Bool → Option (A × List Bool))
    (xs : List Bool) : Option ((Option Bool → A) × List Bool) := do
  let (a, xs) ← read xs
  let (b, xs) ← read xs
  let (c, xs) ← read xs
  pure ((fun s => match s with | none => a | some false => b | some true => c), xs)

/-- Read a fixed-size vector. Its caller checks the minimum total input length
before invoking it; a malformed field also aborts immediately. -/
def codeReadVec {A : Type} (read : List Bool → Option (A × List Bool)) :
    (n : ℕ) → List Bool → Option ((Fin n → A) × List Bool)
  | 0, xs => some (Fin.elim0, xs)
  | n + 1, xs => do
    let (a, xs) ← read xs
    let (as, xs) ← codeReadVec read n xs
    pure (Fin.cases a as, xs)

/-- Interpret a least-significant-bit-first word. Canonical syntax is checked
separately, so this function also has a value on noncanonical words. -/
def codeBitsNat (xs : List Bool) : ℕ := xs.foldr Nat.bit 0

/-- The fallback is the one-state, immediately halting, silent machine. -/
def codeFallback : CodeTM :=
  ⟨0, ⟨0, fun _ _ _ => ⟨.zero, fun _ => (none, .zero), none, none⟩⟩⟩

/-- Reading an encoded bounded index is an exact prefix inverse. -/
lemma codeReadFin_append {n : ℕ} (i : Fin n) (xs : List Bool) :
    codeReadFin n (unaryFin i ++ xs) = some (i, xs) := by
  simp [codeReadFin, unaryFin, List.append_assoc, codeReadUnary_append, i.isLt]

/-- Reading an encoded head movement is an exact prefix inverse. -/
lemma codeReadSign_append (s : SignType) (xs : List Bool) :
    codeReadSign (signBits s ++ xs) = some (s, xs) := by
  cases s <;> rfl

/-- Reading an encoded optional output is an exact prefix inverse. -/
lemma codeReadOutput_append (b : Option Bool) (xs : List Bool) :
    codeReadOutput (optBoolBits b ++ xs) = some (b, xs) := by
  rcases b with _ | b
  · rfl
  · cases b <;> rfl

/-- Reading an encoded optional write is an exact prefix inverse. -/
lemma codeReadWrite_append (b : Option (Option Bool)) (xs : List Bool) :
    codeReadWrite (optOptBoolBits b ++ xs) = some (b, xs) := by
  rcases b with _ | (_ | b)
  · rfl
  · rfl
  · cases b <;> rfl

/-- Reading an encoded successor is an exact prefix inverse. -/
lemma codeReadState_append {n : ℕ} (s : Option (Fin n)) (xs : List Bool) :
    codeReadState n (optStateBits s ++ xs) = some (s, xs) := by
  cases s with
  | none => rfl
  | some s => simp [optStateBits, codeReadState, codeReadFin_append]

/-- Three prefix inverses assemble in the required blank/false/true order. -/
lemma codeReadSymbols_append {A : Type}
    (read : List Bool → Option (A × List Bool)) (write : A → List Bool)
    (h : ∀ a xs, read (write a ++ xs) = some (a, xs))
    (f : Option Bool → A) (xs : List Bool) :
    codeReadSymbols read
      (([none, some false, some true] : List (Option Bool)).flatMap
        (fun s => write (f s)) ++ xs) = some (f, xs) := by
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc, codeReadSymbols, h, bind, Option.bind, pure]
  congr 2
  funext s
  rcases s with _ | b
  · rfl
  · cases b <;> rfl

/-- Fixed-size vector parsing is a prefix inverse of enumeration-order writing.
**Proof sketch.** Induct on the vector length. Read its first entry using the
supplied inverse, then its tail by induction. Finite-function extensionality
identifies the reconstructed head/tail function with the original vector.

**Proof sketch.** Induct on the vector length. The first field reader recovers the head and leaves the concatenated tail; the induction hypothesis recovers the remaining vector. Extensionality identifies the reconstructed function on bounded indices. -/
lemma codeReadVec_append {A : Type}
    (read : List Bool → Option (A × List Bool)) (write : A → List Bool)
    (h : ∀ a xs, read (write a ++ xs) = some (a, xs)) :
    ∀ n (f : Fin n → A) xs,
      codeReadVec read n ((List.finRange n).flatMap (fun i => write (f i)) ++ xs) =
        some (f, xs) := by
  intro n
  induction n with
  | zero =>
    intro f xs
    simp only [List.finRange_zero, List.flatMap_nil, List.nil_append, codeReadVec]
    congr 2
    funext i
    exact i.elim0
  | succ n ih =>
    intro f xs
    simp only [List.finRange_succ, List.flatMap_cons, List.flatMap_map,
      List.append_assoc, codeReadVec, h, bind, Option.bind, ih, pure]
    congr 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Binary reconstruction inverts the canonical little-endian representation,
including the empty representation of zero. -/
lemma codeBitsNat_bits (n : ℕ) : codeBitsNat n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [codeBitsNat]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    simpa only [codeBitsNat, List.foldr_cons] using congrArg (Nat.bit b) ih

/-- Concatenating words with a common length lower bound preserves that bound. -/
lemma codeFlatMap_length {A : Type} (xs : List A) (f : A → List Bool)
    (c : ℕ) (h : ∀ a ∈ xs, c ≤ (f a).length) :
    c * xs.length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_add,
      Nat.mul_one]
    omega

/-- Successful unary parsing characterizes the exact consumed prefix.

**Proof sketch.** Induct on the input. A false bit terminates the number immediately; a true bit increments the recursively recovered number. Empty input cannot succeed. -/
lemma codeReadUnary_sound (xs : List Bool) (n : ℕ) (rest : List Bool)
    (h : codeReadUnary xs = some (n, rest)) :
    xs = List.replicate n true ++ false :: rest := by
  induction xs generalizing n with
  | nil => simp [codeReadUnary] at h
  | cons b xs ih =>
    cases b with
    | false =>
      simp only [codeReadUnary, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | true =>
      cases hr : codeReadUnary xs with
      | none => simp [codeReadUnary, hr] at h
      | some p =>
        rcases p with ⟨k, tail⟩
        simp only [codeReadUnary, hr, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp [List.replicate_succ, ih k hr]

/-- Successful bounded-index parsing determines its complete unary prefix. -/
lemma codeReadFin_sound {n : ℕ} (xs : List Bool) (i : Fin n) (rest : List Bool)
    (h : codeReadFin n xs = some (i, rest)) : xs = unaryFin i ++ rest := by
  obtain ⟨⟨j, tail⟩, hj, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simpa [unaryFin, List.append_assoc] using codeReadUnary_sound xs j tail hj
  · contradiction

/-- A successful movement read consumes precisely its two-bit dictionary entry. -/
lemma codeReadSign_sound (xs : List Bool) (s : SignType) (rest : List Bool)
    (h : codeReadSign xs = some (s, rest)) : xs = signBits s ++ rest := by
  rcases xs with _ | ⟨b, _ | ⟨c, tail⟩⟩
  · simp [codeReadSign] at h
  · cases b <;> simp [codeReadSign] at h
  · cases b <;> cases c <;>
      simp only [codeReadSign, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    all_goals first | contradiction | (rcases h with ⟨rfl, rfl⟩; rfl)

/-- A successful output read consumes precisely its two-bit dictionary entry. -/
lemma codeReadOutput_sound (xs : List Bool) (b : Option Bool) (rest : List Bool)
    (h : codeReadOutput xs = some (b, rest)) : xs = optBoolBits b ++ rest := by
  rcases xs with _ | ⟨a, _ | ⟨c, tail⟩⟩
  · simp [codeReadOutput] at h
  · cases a <;> simp [codeReadOutput] at h
  · cases a <;> cases c <;>
      simp only [codeReadOutput, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    all_goals first | contradiction | (rcases h with ⟨rfl, rfl⟩; rfl)

/-- A successful write read consumes precisely its two-bit dictionary entry. -/
lemma codeReadWrite_sound (xs : List Bool) (b : Option (Option Bool)) (rest : List Bool)
    (h : codeReadWrite xs = some (b, rest)) : xs = optOptBoolBits b ++ rest := by
  rcases xs with _ | ⟨a, _ | ⟨c, tail⟩⟩
  · simp [codeReadWrite] at h
  · cases a <;> simp [codeReadWrite] at h
  · cases a <;> cases c <;>
      simp only [codeReadWrite, Option.some.injEq, Prod.mk.injEq] at h
    all_goals rcases h with ⟨rfl, rfl⟩; rfl

/-- A successful successor read consumes exactly its halt/live unary field.

**Proof sketch.** Split the leading tag. A false tag is exactly the halted state encoding; a true tag delegates to the soundness of the bounded unary reader. Empty input is rejected. -/
lemma codeReadState_sound {n : ℕ} (xs : List Bool) (s : Option (Fin n))
    (rest : List Bool) (h : codeReadState n xs = some (s, rest)) :
    xs = optStateBits s ++ rest := by
  rcases xs with _ | ⟨b, tail⟩
  · simp [codeReadState] at h
  · cases b with
    | false =>
      simp only [codeReadState, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | true =>
      cases hr : codeReadFin n tail with
      | none => simp [codeReadState, hr] at h
      | some p =>
        rcases p with ⟨i, suffix⟩
        simp only [codeReadState, hr, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp only [optStateBits, List.cons_append]
        exact congrArg (List.cons true) (codeReadFin_sound tail i suffix hr)

/-- Three sound prefix readers reconstruct the symbol-indexed row they consumed. -/
lemma codeReadSymbols_sound {A : Type}
    (read : List Bool → Option (A × List Bool)) (write : A → List Bool)
    (sound : ∀ xs a rest, read xs = some (a, rest) → xs = write a ++ rest)
    (xs : List Bool) (f : Option Bool → A) (rest : List Bool)
    (h : codeReadSymbols read xs = some (f, rest)) :
    xs = ([none, some false, some true] : List (Option Bool)).flatMap
      (fun s => write (f s)) ++ rest := by
  simp only [codeReadSymbols, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨a, r₁⟩, h₁, ⟨⟨b, r₂⟩, h₂, ⟨⟨c, r₃⟩, h₃, h⟩⟩⟩ := h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rw [sound xs a r₁ h₁, sound r₁ b r₂ h₂, sound r₂ c r₃ h₃]
  simp [List.append_assoc]

/-- Sound vector parsing reconstructs the entire consumed enumeration.
**Proof sketch.** Induct on the requested vector length. The first successful
entry determines a prefix and the induction hypothesis determines the tail;
the finite-vector constructor enumerates them in exactly that order.

**Proof sketch.** Induct on the number of entries. Successful parsing splits into a successful head parse and a successful tail parse. Their soundness equations concatenate in the same order as the bounded-state enumeration. -/
lemma codeReadVec_sound {A : Type}
    (read : List Bool → Option (A × List Bool)) (write : A → List Bool)
    (sound : ∀ xs a rest, read xs = some (a, rest) → xs = write a ++ rest) :
    ∀ n xs (f : Fin n → A) rest, codeReadVec read n xs = some (f, rest) →
      xs = (List.finRange n).flatMap (fun i => write (f i)) ++ rest := by
  intro n
  induction n with
  | zero =>
    intro xs f rest h
    simpa only [codeReadVec, Option.some.injEq, Prod.mk.injEq,
      List.finRange_zero, List.flatMap_nil, List.nil_append] using
      (show xs = rest from congrArg Prod.snd (Option.some.inj h))
  | succ n ih =>
    intro xs f rest h
    simp only [codeReadVec, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨a, r₁⟩, h₁, ⟨⟨as, r₂⟩, h₂, h⟩⟩ := h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rw [sound xs a r₁ h₁, ih r₁ as r₂ h₂]
    simp [List.finRange_succ, List.flatMap_map, List.append_assoc]

/-- Erased readers keep only the unconsumed suffix. -/
def codeSkipPair (valid : Bool → Bool → Bool) (xs : List Bool) : Option (List Bool) :=
  xs.casesOn none fun a ys => ys.casesOn none fun b zs => if valid a b then some zs else none

/-- Skip a range-checked unary index, keeping only the unconsumed suffix. -/
def codeSkipFin (n : ℕ) (xs : List Bool) : Option (List Bool) :=
  (codeReadUnary xs).bind fun p => if p.1 < n then some p.2 else none

/-- Skip a halt tag or live successor field, keeping only the unconsumed suffix. -/
def codeSkipState (n : ℕ) (xs : List Bool) : Option (List Bool) :=
  xs.casesOn none fun b ys => if b then codeSkipFin n ys else some ys

/-- Skip one five-field transition record, keeping only the unconsumed suffix. -/
def codeSkipAction (n : ℕ) (xs : List Bool) : Option (List Bool) := do
  let xs ← codeSkipPair (fun a b => a || !b) xs
  let xs ← codeSkipPair (fun _ _ => true) xs
  let xs ← codeSkipPair (fun a b => a || !b) xs
  let xs ← codeSkipPair (fun a b => a || !b) xs
  codeSkipState (n + 1) xs

/-- Iterate a skipping reader a fixed number of times, keeping only the final suffix. -/
def codeSkipRepeat (r : List Bool → Option (List Bool)) : ℕ → List Bool → Option (List Bool)
  | 0, xs => some xs
  | n + 1, xs => (r xs).bind (codeSkipRepeat r n)

/-- Erasing the decoded value of the bounded unary reader leaves exactly the public
skipper: `codeReadFin n` erases to `codeSkipFin n`. -/
lemma codeEraseFin (n : ℕ) (xs : List Bool) :
    (codeReadFin n xs).map Prod.snd = codeSkipFin n xs := by
  simp only [codeReadFin, codeSkipFin, bind, Option.map_bind, Function.comp_def]
  congr 1
  funext p
  split <;> rfl

/-- Erasing the decoded value of the movement-dictionary reader leaves the public
two-bit skipper `codeSkipPair (fun a b => a || !b)`. -/
lemma codeEraseSign (xs : List Bool) :
    (codeReadSign xs).map Prod.snd = codeSkipPair (fun a b => a || !b) xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> rfl
    | cons b xs => cases a <;> cases b <;> rfl

/-- Erasing the decoded value of the output-dictionary reader leaves the public
two-bit skipper `codeSkipPair (fun a b => a || !b)`. -/
lemma codeEraseOutput (xs : List Bool) :
    (codeReadOutput xs).map Prod.snd = codeSkipPair (fun a b => a || !b) xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> rfl
    | cons b xs => cases a <;> cases b <;> rfl

/-- Erasing the decoded value of the optional-write reader leaves the unconditional
two-bit skipper `codeSkipPair (fun _ _ => true)`. -/
lemma codeEraseWrite (xs : List Bool) :
    (codeReadWrite xs).map Prod.snd = codeSkipPair (fun _ _ => true) xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> rfl
    | cons b xs => cases a <;> cases b <;> rfl

/-- Erasing the decoded value of the successor-state reader leaves the public
skipper `codeSkipState n`. -/
lemma codeEraseState (n : ℕ) (xs : List Bool) :
    (codeReadState n xs).map Prod.snd = codeSkipState n xs := by
  cases xs with
  | nil => rfl
  | cons b xs =>
    cases b
    · rfl
    · simpa only [codeReadState, codeSkipState, ↓reduceIte,
        Option.map_map, Function.comp_def] using codeEraseFin n xs

/-- A continuation that reads only the unconsumed suffix commutes with erasing the
decoded value: `r.bind (fun p => f p.2) = (r.map Prod.snd).bind f`. -/
lemma codeErase_bind {A B : Type} (r : Option (A × List Bool))
    (f : List Bool → Option B) :
    r.bind (fun p => f p.2) = (r.map Prod.snd).bind f := by
  cases r <;> rfl

/-- Erasing the decoded values of the three-entry symbol-row reader gives the
threefold repetition of the erased entry reader. -/
lemma codeEraseSymbols {A : Type} (r : List Bool → Option (A × List Bool)) (xs : List Bool) :
    (codeReadSymbols r xs).map Prod.snd = codeSkipRepeat (fun s => (r s).map Prod.snd) 3 xs := by
  simp only [codeReadSymbols, bind, Option.map_bind, Function.comp_def, pure, Option.map_some,
    codeSkipRepeat, Option.bind_map]

/-- Erasing the decoded values of the `n`-entry table reader gives the `n`-fold
repetition of the erased entry reader. -/
lemma codeEraseVec {A : Type} (r : List Bool → Option (A × List Bool)) (n : ℕ) :
    ∀ xs, (codeReadVec r n xs).map Prod.snd = codeSkipRepeat (fun s => (r s).map Prod.snd) n xs := by
  induction n with
  | zero => intro xs; rfl
  | succ n ih =>
    intro xs
    simp only [codeReadVec, bind, Option.map_bind, Function.comp_def, pure, Option.map_some]
    have inner (p : A × List Bool) :
        (codeReadVec r n p.2).bind (fun q => some q.2) = codeSkipRepeat (fun s => (r s).map Prod.snd) n p.2 := by
      simpa only [Option.map_eq_bind, Function.comp_def] using ih p.2
    simp only [inner, codeErase_bind, codeSkipRepeat]

end Turing
