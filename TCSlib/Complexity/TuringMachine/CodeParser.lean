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

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, pp. 19-20.)
-/

namespace Turing

/-- Read a unary natural, stopping at its first false bit. -/
def codeReadUnary : List Bool → Option (ℕ × List Bool)
  | false :: xs => some (0, xs)
  | true :: xs => (codeReadUnary xs).map fun p => (p.1 + 1, p.2)
  | [] => none

/-- The unary reader leaves an arbitrary suffix untouched. -/
private lemma codeReadUnary_append (n : ℕ) (xs : List Bool) :
    codeReadUnary (List.replicate n true ++ false :: xs) = some (n, xs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [List.replicate_succ, codeReadUnary] using
      congrArg (Option.map fun p : ℕ × List Bool => (p.1 + 1, p.2)) ih

/-- A unary index is accepted only when it belongs to the declared state space. -/
private def codeReadFin (n : ℕ) (xs : List Bool) : Option (Fin n × List Bool) := do
  let (i, rest) ← codeReadUnary xs
  if h : i < n then some (⟨i, h⟩, rest) else none

/-- Decode the fixed dictionary for a head movement. -/
private def codeReadSign : List Bool → Option (SignType × List Bool)
  | true :: true :: xs => some (.neg, xs)
  | false :: false :: xs => some (.zero, xs)
  | true :: false :: xs => some (.pos, xs)
  | _ => none

/-- Decode the fixed dictionary for an optional output bit. -/
private def codeReadOutput : List Bool → Option (Option Bool × List Bool)
  | false :: false :: xs => some (none, xs)
  | true :: false :: xs => some (some false, xs)
  | true :: true :: xs => some (some true, xs)
  | _ => none

/-- Decode the fixed dictionary for an optional work-tape write. -/
private def codeReadWrite : List Bool → Option (Option (Option Bool) × List Bool)
  | false :: false :: xs => some (none, xs)
  | false :: true :: xs => some (some none, xs)
  | true :: false :: xs => some (some (some false), xs)
  | true :: true :: xs => some (some (some true), xs)
  | _ => none

/-- Read the halt tag or a range-checked live successor state. -/
private def codeReadState (n : ℕ) : List Bool → Option (Option (Fin n) × List Bool)
  | false :: xs => some (none, xs)
  | true :: xs => (codeReadFin n xs).map fun p => (some p.1, p.2)
  | [] => none

/-- Read the five fields of a transition, failing as soon as any field fails. -/
private def codeReadAction (n : ℕ) (xs : List Bool) :
    Option (Action 1 Bool (Fin (n + 1)) × List Bool) := do
  let (im, xs) ← codeReadSign xs
  let (wr, xs) ← codeReadWrite xs
  let (wm, xs) ← codeReadSign xs
  let (out, xs) ← codeReadOutput xs
  let (q, xs) ← codeReadState (n + 1) xs
  pure (⟨im, fun _ => (wr, wm), out, q⟩, xs)

/-- Read one entry for each tape symbol, in blank/false/true order. -/
private def codeReadSymbols {A : Type} (read : List Bool → Option (A × List Bool))
    (xs : List Bool) : Option ((Option Bool → A) × List Bool) := do
  let (a, xs) ← read xs
  let (b, xs) ← read xs
  let (c, xs) ← read xs
  pure ((fun s => match s with | none => a | some false => b | some true => c), xs)

/-- Read a fixed-size vector. Its caller checks the minimum total input length
before invoking it; a malformed field also aborts immediately. -/
private def codeReadVec {A : Type} (read : List Bool → Option (A × List Bool)) :
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

/-- Parse the exact serialization grammar of the phase-3 re-audit, Argument A.
The length guard precedes vector recursion: every state requires nine records,
each containing at least nine bits. The suffix must consist entirely of true bits. -/
private def codeParse (xs : List Bool) : Option CodeTM := do
  let (bits, rest) ← pairDecode xs
  let n := codeBitsNat bits
  if bits ≠ n.bits then none else do
    if 81 * (n + 1) > rest.length then none else do
      let (q, rest) ← codeReadFin (n + 1) rest
      let (table, rest) ← codeReadVec
        (codeReadSymbols (codeReadSymbols (codeReadAction n))) (n + 1) rest
      if rest.all id then
        pure ⟨n, ⟨q, fun s inp w => table s inp (w 0)⟩⟩
      else none

/-- Total decoding: every malformed string denotes the fixed fallback. -/
def codeDecode (xs : List Bool) : CodeTM := (codeParse xs).getD codeFallback

/-- Reading an encoded bounded index is an exact prefix inverse. -/
private lemma codeReadFin_append {n : ℕ} (i : Fin n) (xs : List Bool) :
    codeReadFin n (unaryFin i ++ xs) = some (i, xs) := by
  simp [codeReadFin, unaryFin, List.append_assoc, codeReadUnary_append, i.isLt]

/-- Reading an encoded head movement is an exact prefix inverse. -/
private lemma codeReadSign_append (s : SignType) (xs : List Bool) :
    codeReadSign (signBits s ++ xs) = some (s, xs) := by
  cases s <;> rfl

/-- Reading an encoded optional output is an exact prefix inverse. -/
private lemma codeReadOutput_append (b : Option Bool) (xs : List Bool) :
    codeReadOutput (optBoolBits b ++ xs) = some (b, xs) := by
  rcases b with _ | b
  · rfl
  · cases b <;> rfl

/-- Reading an encoded optional write is an exact prefix inverse. -/
private lemma codeReadWrite_append (b : Option (Option Bool)) (xs : List Bool) :
    codeReadWrite (optOptBoolBits b ++ xs) = some (b, xs) := by
  rcases b with _ | (_ | b)
  · rfl
  · rfl
  · cases b <;> rfl

/-- Reading an encoded successor is an exact prefix inverse. -/
private lemma codeReadState_append {n : ℕ} (s : Option (Fin n)) (xs : List Bool) :
    codeReadState n (optStateBits s ++ xs) = some (s, xs) := by
  cases s with
  | none => rfl
  | some s => simp [optStateBits, codeReadState, codeReadFin_append]

/-- All five fields round-trip, including the unique work-tape coordinate. -/
private lemma codeReadAction_append {n : ℕ} (a : Action 1 Bool (Fin (n + 1)))
    (xs : List Bool) : codeReadAction n (actionBits a ++ xs) = some (a, xs) := by
  simp only [actionBits, List.append_assoc, codeReadAction, codeReadSign_append,
    codeReadWrite_append, codeReadOutput_append, codeReadState_append,
    bind, Option.bind, pure]
  congr 2
  cases a
  congr
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

/-- Three prefix inverses assemble in the required blank/false/true order. -/
private lemma codeReadSymbols_append {A : Type}
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
private lemma codeReadVec_append {A : Type}
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
private lemma codeBitsNat_bits (n : ℕ) : codeBitsNat n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [codeBitsNat]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    simpa only [codeBitsNat, List.foldr_cons] using congrArg (Nat.bit b) ih

/-- Every record has eight fixed bits and a nonempty successor field. -/
private lemma codeAction_length {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    9 ≤ (actionBits a).length := by
  have hs (s : SignType) : (signBits s).length = 2 := by cases s <;> rfl
  have ho (b : Option Bool) : (optBoolBits b).length = 2 := by
    rcases b with _ | b
    · rfl
    · cases b <;> rfl
  have hw (b : Option (Option Bool)) : (optOptBoolBits b).length = 2 := by
    rcases b with _ | (_ | b)
    · rfl
    · rfl
    · cases b <;> rfl
  have hq : 1 ≤ (optStateBits a.state).length := by
    cases a.state <;> simp [optStateBits, unaryFin]
  simp only [actionBits, List.length_append, hs, ho, hw]
  omega

/-- Concatenating words with a common length lower bound preserves that bound. -/
private lemma codeFlatMap_length {A : Type} (xs : List A) (f : A → List Bool)
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

/-- The complete table contains at least 81 bits per live state.

**Proof sketch.** Every action contains eight fixed field bits and at least one successor bit. Summing this lower bound over the three work symbols, three input symbols, and all states gives at least 81 bits per state. -/
private lemma codeTable_length (M : CodeTM) :
    81 * (M.numStates + 1) ≤
      ((List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
            actionBits (M.tm.tr q inp fun _ => w)).length := by
  have h := codeFlatMap_length (List.finRange (M.numStates + 1))
    (fun q => ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
        actionBits (M.tm.tr q inp fun _ => w)) 81 (by
      intro q _
      have h := codeFlatMap_length ([none, some false, some true] : List (Option Bool))
        (fun inp => ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
          actionBits (M.tm.tr q inp fun _ => w)) 27 (by
            intro inp _
            simpa using codeFlatMap_length
              ([none, some false, some true] : List (Option Bool))
              (fun w => actionBits (M.tm.tr q inp fun _ => w)) 9
              (fun _ _ => codeAction_length _))
      simpa using h)
  simpa using h

/-- The table reader recovers every transition. Blank/false/true exhaust each
read alphabet; a one-work-tape read vector is determined by its zero coordinate. -/
private lemma codeReadTable_append (M : CodeTM) (xs : List Bool) :
    codeReadVec (codeReadSymbols (codeReadSymbols (codeReadAction M.numStates)))
      (M.numStates + 1)
      (((List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
            actionBits (M.tm.tr q inp fun _ => w)) ++ xs) =
      some ((fun q inp w => M.tm.tr q inp (fun _ => w)), xs) :=
  codeReadVec_append _ _
    (fun _ _ => codeReadSymbols_append _ _
      (fun _ _ => codeReadSymbols_append _ _ codeReadAction_append _ _) _ _) _ _ _

/-- The complete parser recovers a serialized machine under arbitrary true padding.
**Proof sketch.** The doubled header recovers the canonical binary count. The
minimum table-length lemma discharges the short-circuit guard. The unary initial
state and enumerated records then round-trip with the padding left untouched.
All remaining bits are true, and extensionality recovers the transition function.

**Proof sketch.** The doubled-bit parser first recovers the canonical state-count bits. The table length bound discharges the early guard; the field and vector inverse laws then recover the initial state and every transition. The remaining replicated true bits pass the suffix test. -/
private lemma codeParse_serialize_pad (M : CodeTM) (m : ℕ) :
    codeParse (M.serialize ++ List.replicate m true) = some M := by
  have hp (a b c : List Bool) : pairEncode a b ++ c = pairEncode a (b ++ c) := by
    simp [pairEncode, List.append_assoc]
  unfold CodeTM.serialize
  rw [hp]
  unfold codeParse
  rw [pairDecode_pairEncode]
  dsimp only [bind, Option.bind]
  rw [codeBitsNat_bits]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  have hlen := codeTable_length M
  simp only [List.length_append, List.length_replicate] at *
  rw [if_neg (by omega)]
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
    codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, or_true,
    ite_self, ↓reduceIte, pure]
  congr 1
  cases M with
  | mk n tm =>
    congr 1
    cases tm with
    | mk q tr =>
      congr 1
      funext s inp w
      apply congrArg (tr s inp)
      funext i
      exact congrArg w (Subsingleton.elim _ _)

/-- The total decoder satisfies the required exact padded round-trip law. -/
lemma codeDecode_serialize_pad (M : CodeTM) (m : ℕ) :
    codeDecode (M.serialize ++ List.replicate m true) = M := by
  simp only [codeDecode, codeParse_serialize_pad, Option.getD_some]

/-- Successful unary parsing characterizes the exact consumed prefix.

**Proof sketch.** Induct on the input. A false bit terminates the number immediately; a true bit increments the recursively recovered number. Empty input cannot succeed. -/
private lemma codeReadUnary_sound (xs : List Bool) (n : ℕ) (rest : List Bool)
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
private lemma codeReadFin_sound {n : ℕ} (xs : List Bool) (i : Fin n) (rest : List Bool)
    (h : codeReadFin n xs = some (i, rest)) : xs = unaryFin i ++ rest := by
  obtain ⟨⟨j, tail⟩, hj, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simpa [unaryFin, List.append_assoc] using codeReadUnary_sound xs j tail hj
  · contradiction

/-- A successful doubled header has exactly the paired form, including empty data.

**Proof sketch.** Induct by the same two-bit steps as the aligned parser. Equal bits extend the doubled prefix, the false/true separator ends it, and all incomplete or forbidden pairs are rejected. -/
private lemma codePairDecode_sound (xs a rest : List Bool)
    (h : pairDecode xs = some (a, rest)) : xs = pairEncode a rest := by
  induction xs using pairDecode.induct generalizing a with
  | case1 xs ih =>
    cases hr : pairDecode xs with
    | none => simp [pairDecode, hr] at h
    | some p =>
      rcases p with ⟨ys, tail⟩
      simp only [pairDecode, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [pairEncode] using congrArg (fun zs => false :: false :: zs) (ih ys hr)
  | case2 xs ih =>
    cases hr : pairDecode xs with
    | none => simp [pairDecode, hr] at h
    | some p =>
      rcases p with ⟨ys, tail⟩
      simp only [pairDecode, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [pairEncode] using congrArg (fun zs => true :: true :: zs) (ih ys hr)
  | case3 xs =>
    simp only [pairDecode, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | case4 xs h₁ h₂ h₃ => simp [pairDecode, h₁, h₂, h₃] at h

/-- A successful movement read consumes precisely its two-bit dictionary entry. -/
private lemma codeReadSign_sound (xs : List Bool) (s : SignType) (rest : List Bool)
    (h : codeReadSign xs = some (s, rest)) : xs = signBits s ++ rest := by
  rcases xs with _ | ⟨b, _ | ⟨c, tail⟩⟩
  · simp [codeReadSign] at h
  · cases b <;> simp [codeReadSign] at h
  · cases b <;> cases c <;>
      simp only [codeReadSign, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    all_goals first | contradiction | (rcases h with ⟨rfl, rfl⟩; rfl)

/-- A successful output read consumes precisely its two-bit dictionary entry. -/
private lemma codeReadOutput_sound (xs : List Bool) (b : Option Bool) (rest : List Bool)
    (h : codeReadOutput xs = some (b, rest)) : xs = optBoolBits b ++ rest := by
  rcases xs with _ | ⟨a, _ | ⟨c, tail⟩⟩
  · simp [codeReadOutput] at h
  · cases a <;> simp [codeReadOutput] at h
  · cases a <;> cases c <;>
      simp only [codeReadOutput, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    all_goals first | contradiction | (rcases h with ⟨rfl, rfl⟩; rfl)

/-- A successful write read consumes precisely its two-bit dictionary entry. -/
private lemma codeReadWrite_sound (xs : List Bool) (b : Option (Option Bool)) (rest : List Bool)
    (h : codeReadWrite xs = some (b, rest)) : xs = optOptBoolBits b ++ rest := by
  rcases xs with _ | ⟨a, _ | ⟨c, tail⟩⟩
  · simp [codeReadWrite] at h
  · cases a <;> simp [codeReadWrite] at h
  · cases a <;> cases c <;>
      simp only [codeReadWrite, Option.some.injEq, Prod.mk.injEq] at h
    all_goals rcases h with ⟨rfl, rfl⟩; rfl

/-- A successful successor read consumes exactly its halt/live unary field.

**Proof sketch.** Split the leading tag. A false tag is exactly the halted state encoding; a true tag delegates to the soundness of the bounded unary reader. Empty input is rejected. -/
private lemma codeReadState_sound {n : ℕ} (xs : List Bool) (s : Option (Fin n))
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

/-- Successful record parsing characterizes its complete serialized prefix.
**Proof sketch.** Decompose the five successful reads, apply the dictionary
inverse to each, and concatenate their consumed prefixes in order. -/
private lemma codeReadAction_sound {n : ℕ} (xs : List Bool)
    (a : Action 1 Bool (Fin (n + 1))) (rest : List Bool)
    (h : codeReadAction n xs = some (a, rest)) : xs = actionBits a ++ rest := by
  simp only [codeReadAction, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨im, r₁⟩, h₁, ⟨⟨wr, r₂⟩, h₂, ⟨⟨wm, r₃⟩, h₃,
    ⟨⟨out, r₄⟩, h₄, ⟨⟨q, r₅⟩, h₅, h⟩⟩⟩⟩⟩ := h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rw [codeReadSign_sound xs im r₁ h₁, codeReadWrite_sound r₁ wr r₂ h₂,
    codeReadSign_sound r₂ wm r₃ h₃, codeReadOutput_sound r₃ out r₄ h₄,
    codeReadState_sound r₄ q r₅ h₅]
  simp [actionBits, List.append_assoc]

/-- Three sound prefix readers reconstruct the symbol-indexed row they consumed. -/
private lemma codeReadSymbols_sound {A : Type}
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
private lemma codeReadVec_sound {A : Type}
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

/-- An all-true suffix is exactly true padding of its own length. -/
private lemma codeAllTrue_eq (xs : List Bool) (h : xs.all id = true) :
    xs = List.replicate xs.length true := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b with
    | false => simp at h
    | true =>
      simp only [List.all_cons, id_eq, Bool.true_and] at h
      simp only [List.length_cons, List.replicate_succ]
      exact congrArg (List.cons true) (ih h)

/-- Acceptance characterizes a canonical serialization followed by true padding.
**Proof sketch.** Successful parsing fixes the count's canonical binary syntax,
the initial state, and every table record. Apply the soundness lemma for each
reader to reconstruct the consumed prefix; the final all-true test reconstructs
the padding. The one-work-tape read function is constant at its zero coordinate.

**Proof sketch.** Decompose a successful parse into its count, initial state, and table. Field soundness reconstructs each consumed prefix. The canonical-bits check fixes the count representation, and the final all-true check identifies the remainder as true padding. -/
private lemma codeParse_sound (xs : List Bool) (M : CodeTM)
    (h : codeParse xs = some M) :
    ∃ m, xs = M.serialize ++ List.replicate m true := by
  unfold codeParse at h
  obtain ⟨⟨bits, rest⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · contradiction
  next hb =>
    have hb : bits = (codeBitsNat bits).bits := not_not.mp hb
    split at h
    · contradiction
    next _ =>
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨q, r₁⟩, hq, ⟨⟨table, r₂⟩, ht, h⟩⟩ := h
      split at h
      next hpad =>
        simp only [pure, Option.some.injEq] at h
        subst M
        refine ⟨r₂.length, ?_⟩
        have htable := codeReadVec_sound _ _
          (fun _ _ _ => codeReadSymbols_sound _ _
            (fun _ _ _ => codeReadSymbols_sound _ _ codeReadAction_sound _ _ _) _ _ _)
          _ _ _ _ ht
        dsimp only at htable hpad
        rw [codePairDecode_sound xs bits rest hp, codeReadFin_sound rest q r₁ hq,
          htable, codeAllTrue_eq r₂ hpad]
        simp only [CodeTM.serialize, pairEncode, List.append_assoc]
        simp only [List.length_replicate]
        congr 1
        exact congrArg (List.flatMap fun b : Bool => [b, b]) hb
      · contradiction

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

private lemma codeEraseFin (n : ℕ) (xs : List Bool) :
    (codeReadFin n xs).map Prod.snd = codeSkipFin n xs := by
  simp only [codeReadFin, codeSkipFin, bind, Option.map_bind, Function.comp_def]
  congr 1
  funext p
  split <;> rfl

private lemma codeEraseSign (xs : List Bool) :
    (codeReadSign xs).map Prod.snd = codeSkipPair (fun a b => a || !b) xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> rfl
    | cons b xs => cases a <;> cases b <;> rfl

private lemma codeEraseOutput (xs : List Bool) :
    (codeReadOutput xs).map Prod.snd = codeSkipPair (fun a b => a || !b) xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> rfl
    | cons b xs => cases a <;> cases b <;> rfl

private lemma codeEraseWrite (xs : List Bool) :
    (codeReadWrite xs).map Prod.snd = codeSkipPair (fun _ _ => true) xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> rfl
    | cons b xs => cases a <;> cases b <;> rfl

private lemma codeEraseState (n : ℕ) (xs : List Bool) :
    (codeReadState n xs).map Prod.snd = codeSkipState n xs := by
  cases xs with
  | nil => rfl
  | cons b xs =>
    cases b
    · rfl
    · simpa only [codeReadState, codeSkipState, ↓reduceIte,
        Option.map_map, Function.comp_def] using codeEraseFin n xs

private lemma codeErase_bind {A B : Type} (r : Option (A × List Bool))
    (f : List Bool → Option B) :
    r.bind (fun p => f p.2) = (r.map Prod.snd).bind f := by
  cases r <;> rfl

private lemma codeEraseAction (n : ℕ) (xs : List Bool) :
    (codeReadAction n xs).map Prod.snd = codeSkipAction n xs := by
  simp only [codeReadAction, codeSkipAction, bind, Option.map_bind, Function.comp_def, pure, Option.map_some]
  rw [← codeEraseSign xs, ← codeErase_bind]
  congr 1; funext p
  rw [← codeEraseWrite p.2, ← codeErase_bind]
  congr 1; funext p
  rw [← codeEraseSign p.2, ← codeErase_bind]
  congr 1; funext p
  rw [← codeEraseOutput p.2, ← codeErase_bind]
  congr 1; funext p
  simpa only [Option.map_eq_bind, Function.comp_def] using codeEraseState (n + 1) p.2

private lemma codeEraseSymbols {A : Type} (r : List Bool → Option (A × List Bool)) (xs : List Bool) :
    (codeReadSymbols r xs).map Prod.snd = codeSkipRepeat (fun s => (r s).map Prod.snd) 3 xs := by
  simp only [codeReadSymbols, bind, Option.map_bind, Function.comp_def, pure, Option.map_some,
    codeSkipRepeat, Option.bind_map]

private lemma codeEraseVec {A : Type} (r : List Bool → Option (A × List Bool)) (n : ℕ) :
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

private def codeParseFull (xs : List Bool) : Option (CodeTM × List Bool) := do
  let (bits, rest) ← pairDecode xs
  let n := codeBitsNat bits
  if bits ≠ n.bits then none else do
    if 81 * (n + 1) > rest.length then none else do
      let (q, rest) ← codeReadFin (n + 1) rest
      let (table, rest) ← codeReadVec
        (codeReadSymbols (codeReadSymbols (codeReadAction n))) (n + 1) rest
      if rest.all id then
        pure (⟨n, ⟨q, fun s inp w => table s inp (w 0)⟩⟩, rest)
      else none

/-- The erased parser: accept exactly the strings the parser accepts, returning only the unconsumed all-true suffix. -/
def codeScan (xs : List Bool) : Option (List Bool) := do
  let (bits, rest) ← pairDecode xs
  let n := codeBitsNat bits
  if bits ≠ n.bits then none else do
    if 81 * (n + 1) > rest.length then none else do
      let rest ← codeSkipFin (n + 1) rest
      let rest ← codeSkipRepeat (codeSkipRepeat (codeSkipRepeat (codeSkipAction n) 3) 3) (n + 1) rest
      if rest.all id then pure rest else none

private lemma codeParse_full (xs : List Bool) : codeParse xs = (codeParseFull xs).map Prod.fst := by
  simp only [codeParse, codeParseFull, bind, Option.map_bind, Function.comp_def]
  congr 1
  funext p
  dsimp only
  split <;> try simp only [Option.map_none]
  split <;> try simp only [Option.map_none, Option.map_bind, Function.comp_def]
  congr 1; funext q
  congr 1; funext t
  dsimp only
  split <;> rfl

private lemma codeScan_full (xs : List Bool) : codeScan xs = (codeParseFull xs).map Prod.snd := by
  simp only [codeScan, codeParseFull, bind, Option.map_bind, Function.comp_def]
  congr 1
  funext p
  dsimp only
  split <;> try simp only [Option.map_none]
  split <;> try simp only [Option.map_none, Option.map_bind, Function.comp_def]
  have h (q : Fin (codeBitsNat p.1 + 1) × List Bool)
      (t : (Fin (codeBitsNat p.1 + 1) → Option Bool → Option Bool → Action 1 Bool (Fin (codeBitsNat p.1 + 1))) × List Bool) :
      (if t.2.all id then some ((⟨codeBitsNat p.1, ⟨q.1, fun s inp w => t.1 s inp (w 0)⟩⟩ : CodeTM), t.2) else none).map Prod.snd =
        (if t.2.all id then some t.2 else none) := by split <;> rfl
  simp only [pure, h]
  rw [← codeEraseFin _ _, ← codeErase_bind]
  congr 1; funext q
  have ht := codeEraseVec (codeReadSymbols (codeReadSymbols (codeReadAction (codeBitsNat p.1))))
    (codeBitsNat p.1 + 1) q.2
  simp only [codeEraseSymbols, codeEraseAction] at ht
  rw [← ht, ← codeErase_bind]

/-- **Proof sketch.** Use the same decomposition as parser soundness, retaining the exact unconsumed suffix. The field soundness equations and the canonical count check reconstruct the original input as the machine serialization followed by that suffix. -/
private lemma codeParseFull_sound (xs : List Bool) (M : CodeTM) (tail : List Bool)
    (h : codeParseFull xs = some (M, tail)) : xs = M.serialize ++ tail := by
  unfold codeParseFull at h
  obtain ⟨⟨bits, rest⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · contradiction
  next hb =>
    have hb : bits = (codeBitsNat bits).bits := not_not.mp hb
    split at h
    · contradiction
    next _ =>
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨q, r₁⟩, hq, ⟨⟨table, r₂⟩, ht, h⟩⟩ := h
      split at h
      next hpad =>
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have htable := codeReadVec_sound _ _
          (fun _ _ _ => codeReadSymbols_sound _ _
            (fun _ _ _ => codeReadSymbols_sound _ _ codeReadAction_sound _ _ _) _ _ _)
          _ _ _ _ ht
        dsimp only at htable
        rw [codePairDecode_sound xs bits rest hp, codeReadFin_sound rest q r₁ hq, htable]
        simp only [CodeTM.serialize, pairEncode, List.append_assoc]
        congr 1
        exact congrArg (List.flatMap fun b : Bool => [b, b]) hb
      · contradiction

/-- The canonical serialization of the machine a string denotes: the consumed prefix on scanner success, the fallback machine's serialization otherwise. -/
def codeCanonical (xs : List Bool) : List Bool :=
  (codeScan xs).casesOn codeFallback.serialize fun tail => xs.take (xs.length - tail.length)

/-- The suffix scanner computes exactly the fixed serialization of the decoded machine. -/
lemma codeCanonical_eq (xs : List Bool) : codeCanonical xs = (codeDecode xs).serialize := by
  unfold codeCanonical codeDecode
  rw [codeScan_full, codeParse_full]
  cases h : codeParseFull xs with
  | none => rfl
  | some p =>
    rcases p with ⟨M, tail⟩
    simp only [Option.map_some, Option.getD_some]
    rw [codeParseFull_sound xs M tail h]
    simp

end Turing
