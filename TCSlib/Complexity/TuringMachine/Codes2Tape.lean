/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.TuringMachine.MathlibBridge
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic two-work-tape machine codes (Z3)

The deterministic code layer currently covers only the one-work-tape
binary normal form (`Turing.CodeTM`/`Turing.MachineCode`/
`Turing.EffectiveMachineCode`, `Encoding.lean`), which is why the received
time hierarchy arrives at `f²` strength (plan §2.1): converting to that
normal form costs a square. This file is §13's Z3: the **deterministic
two-work-tape** code scheme, the codes the two-work-tape universal machine
(stage 1, plan §4b) reads, over **the same `Turing.actionBits₂` record
format** that `Turing.CodeNDTM` fixed for the nondeterministic two-tape
codes (design §13a: one branch instead of two — never a second
serialization). The file name reads *codes for two-tape machines*
(decision 13.3, renamed from `Codes2` by the user).

Mirrors: `Turing.CodeTM` → `Turing.Code2TM`; `Turing.MachineCode` →
`Turing.MachineCode2`; `Turing.EffectiveMachineCode` →
`Turing.EffectiveMachineCode2`; and, per the P3.2 lesson (a variable-code
consumer needs uniformly timed decoding — `EffectiveMachineCode` bounds no
decoding time), `UniformMachineCode` (`Diagonalization/EXPCOM.lean`) →
`Turing.UniformMachineCode2`.

## Status: statement skeleton (§13 statement phase, tranche A-S2)

The structures and serialization are real definitions; the two existence
statements are `sorry`d with proof sketches naming the received routes.

## Main definitions and results

* `Turing.Code2TM`, `Turing.Code2TM.serialize` — the deterministic
  two-work-tape normal form and its fixed, scheme-independent
  serialization (27 `Turing.actionBits₂` records per state: three input
  reads by three reads on each of the two work tapes).
* `Turing.MachineCode2`, `Turing.EffectiveMachineCode2`,
  `Turing.UniformMachineCode2` — the scheme laws, the effective scheme,
  and the uniformly timed scheme.
* `Turing.exists_effectiveMachineCode2`,
  `Turing.exists_uniformMachineCode2` — the sorried existence statements.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern
  Approach*, Cambridge University Press, 2009. (§1.4, machine codes;
  §1.7/§3.1 for the two-tape consumer.)

**ZF-B status appendix.** The skeleton-status text above records the received
statement phase. `exists_effectiveMachineCode2` is now proved; the uniform
simulator remains the continuation target. The new implementation includes
private adaptations of inaccessible helpers in `CodeParser.lean` and
`MathlibBridge.lean`, with declaration-level provenance in `REPORT.md`.

**ZF-B2 cleanup appendix.** The ZF-B provenance above records the original
delivery. Its 46 format-independent local copies have now been deleted:
all uses cite the promoted public readers and primitive-recursion lemmas.
The 24 remaining private declarations implement the two-tape format and
its 354-bit regression; their one-tape counterparts and retained proof
material are itemized in this delivery's duplication ledger.
-/

namespace Turing

/-- The coded normal form of a deterministic machine with **two** work
tapes: a binary-alphabet machine with state space `Fin (numStates + 1)`
(never empty). Two work tapes, not one, because the Hennie-Stearns
conversion lands there at `O(T log T)` and the two-tape universal machine
(its consumer) runs such codes at linear overhead — the whole point of
strengthening past `Turing.CodeTM`'s square. Mirrors `Turing.CodeTM` and
`Turing.CodeNDTM`. [AB09, §1.4, §1.7] -/
structure Code2TM where
  /-- one less than the number of states (so the state space is never empty) -/
  numStates : ℕ
  /-- the underlying two-work-tape deterministic machine -/
  tm : MultiTapeTM 2 Bool (Fin (numStates + 1))

/-- The bundled machine of a coded two-tape machine. -/
def Code2TM.toFinTM (M : Code2TM) : FinTM Bool where
  k := 2
  State := Fin (M.numStates + 1)
  tm := M.tm

/-- The **fixed, scheme-independent** canonical serialization, mirroring
`Turing.CodeTM.serialize` and `Turing.CodeNDTM.serialize` over the same
`Turing.actionBits₂` record: the state count, the initial state, then the
full transition table in the fixed enumeration order — states in `Fin`
order, then the input read and the two work reads each over `none`,
`some false`, `some true` (27 records per state; the nondeterministic
table's outermost choice bit is absent). This is the target format of
`Turing.EffectiveMachineCode2.canonizer` and the input format of the
two-work-tape universal machine. -/
def Code2TM.serialize (M : Code2TM) : List Bool :=
  pairEncode (Nat.bits M.numStates)
    (unaryFin M.tm.q₀ ++
      (List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w₀ =>
            ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
              actionBits₂ (M.tm.tr q inp (workPair w₀ w₁)))

/-- The algebraic laws of a representation scheme for coded two-tape
machines, mirroring `Turing.MachineCode` [AB09, §1.4]: a total decoding
(property 1), an encoding, and recovery under arbitrary `true`-padding
(property 2 — every machine has infinitely many representations). -/
structure MachineCode2 where
  /-- encode a machine as a binary string -/
  encode : Code2TM → List Bool
  /-- decode any binary string to a machine (total by type: property 1) -/
  decode : List Bool → Code2TM
  /-- a code followed by any amount of `true`-padding decodes to the
  machine (property 2) -/
  decode_encode_pad : ∀ M m, decode (encode M ++ List.replicate m true) = M

/-- Decoding a code recovers the machine (padding by zero symbols).
Skeleton-time proof, mirroring `Turing.MachineCode.decode_encode`. -/
theorem MachineCode2.decode_encode (c : MachineCode2) (M : Code2TM) :
    c.decode (c.encode M) = M := by
  simpa using c.decode_encode_pad M 0

/-- An *effective* representation scheme for two-tape machines: the
algebraic laws together with a machine of this development computing the
fixed serialization of the decoded machine — the mirror of
`Turing.EffectiveMachineCode`, with the same Argument-A rationale (the
target `Turing.Code2TM.serialize` is scheme-independent). As there, the
canonizer's time bound is arbitrary: fixed-code consumers absorb it into
their constants, and variable-code consumers must use
`Turing.UniformMachineCode2` instead. -/
structure EffectiveMachineCode2 extends MachineCode2 where
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's (arbitrary) time bound -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serialize ∘ decode` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => (decode α).serialize) canonizerTime

/-! ### Private parser and canonizer implementation (ZF-B)

This retargets the received `CodeParser` field/vector architecture to the
seven-field two-tape record. The inaccessible private parser and primitive
recursion lemmas are locally adapted under the exclusive-file rule; each is
itemized in the delivery's duplication ledger. Public field encodings, the
unary reader, suffix-skipping primitives, pairing laws, and `codePrim_machine`
are cited directly. No ND existence theorem is used.

ZF-B2 now cites all 46 promoted format-independent declarations directly.
Only the two-tape-specific adaptations and the regression remain local.
-/



/-- Read the seven fields of a transition, failing as soon as any field fails. -/
private def zfBReadAction (n : ℕ) (xs : List Bool) :
    Option (Action 2 Bool (Fin (n + 1)) × List Bool) := do
  let (im, xs) ← codeReadSign xs
  let (wr, xs) ← codeReadWrite xs
  let (wm, xs) ← codeReadSign xs
  let (wr₁, xs) ← codeReadWrite xs
  let (wm₁, xs) ← codeReadSign xs
  let (out, xs) ← codeReadOutput xs
  let (q, xs) ← codeReadState (n + 1) xs
  pure (⟨im, fun i => if i = 0 then (wr, wm) else (wr₁, wm₁), out, q⟩, xs)

/-- The fallback is the one-state, immediately halting, silent machine. -/
private def zfBFallback : Code2TM :=
  ⟨0, ⟨0, fun _ _ _ => ⟨.zero, fun _ => (none, .zero), none, none⟩⟩⟩

/-- The one-state halting fallback has the audited 354-bit serialization.
The closed computation includes its header and all 27 thirteen-bit records. -/
private lemma zfBFallback_serialize_length : zfBFallback.serialize.length = 354 := by
  unfold Code2TM.serialize
  dsimp only [zfBFallback]
  set_option maxRecDepth 10000 in
    norm_num [length_pairEncode, unaryFin, actionBits₂, signBits, optOptBoolBits,
      optBoolBits, optStateBits, List.finRange_succ, List.finRange_zero]

/-- Parse the exact serialization grammar of the phase-3 re-audit, Argument A.
The length guard precedes vector recursion: every state requires 27 records,
each containing at least thirteen bits. The suffix must consist entirely of true bits. -/
private def zfBParse (xs : List Bool) : Option Code2TM := do
  let (bits, rest) ← pairDecode xs
  let n := codeBitsNat bits
  if bits ≠ n.bits then none else do
    if 351 * (n + 1) > rest.length then none else do
      let (q, rest) ← codeReadFin (n + 1) rest
      let (table, rest) ← codeReadVec
        (codeReadSymbols (codeReadSymbols (codeReadSymbols (zfBReadAction n)))) (n + 1) rest
      if rest.all id then
        pure ⟨n, ⟨q, fun s inp w => table s inp (w 0) (w 1)⟩⟩
      else none

/-- Total decoding: every malformed string denotes the fixed fallback. -/
private def zfBDecode (xs : List Bool) : Code2TM := (zfBParse xs).getD zfBFallback

/-- All seven fields round-trip, including both work-tape coordinates. -/
private lemma zfBReadAction_append {n : ℕ} (a : Action 2 Bool (Fin (n + 1)))
    (xs : List Bool) : zfBReadAction n (actionBits₂ a ++ xs) = some (a, xs) := by
  simp only [actionBits₂, List.append_assoc, zfBReadAction, codeReadSign_append,
    codeReadWrite_append, codeReadOutput_append, codeReadState_append,
    bind, Option.bind, pure]
  congr 2
  cases a
  congr
  funext i
  fin_cases i <;> rfl

/-- Every record has twelve fixed bits and a nonempty successor field. -/
private lemma zfBAction_length {n : ℕ} (a : Action 2 Bool (Fin (n + 1))) :
    13 ≤ (actionBits₂ a).length := by
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
  simp only [actionBits₂, List.length_append, hs, ho, hw]
  omega

/-- The complete table contains at least 351 bits per live state.

**Proof sketch.** Every action contains twelve fixed field bits and at least one successor bit. Summing this lower bound over the three symbols for each work tape, three input symbols, and all states gives at least 351 bits per state. -/
private lemma zfBTable_length (M : Code2TM) :
    351 * (M.numStates + 1) ≤
      ((List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w₀ =>
            ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
              actionBits₂ (M.tm.tr q inp (workPair w₀ w₁))).length := by
  have h := codeFlatMap_length (List.finRange (M.numStates + 1))
    (fun q => ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun w₀ =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
          actionBits₂ (M.tm.tr q inp (workPair w₀ w₁))) 351 (by
      intro q _
      have h := codeFlatMap_length ([none, some false, some true] : List (Option Bool))
        (fun inp => ([none, some false, some true] : List (Option Bool)).flatMap fun w₀ =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
            actionBits₂ (M.tm.tr q inp (workPair w₀ w₁))) 117 (by
          intro inp _
          have h := codeFlatMap_length ([none, some false, some true] : List (Option Bool))
            (fun w₀ => ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
              actionBits₂ (M.tm.tr q inp (workPair w₀ w₁))) 39 (by
                intro w₀ _
                simpa using codeFlatMap_length
                  ([none, some false, some true] : List (Option Bool))
                  (fun w₁ => actionBits₂ (M.tm.tr q inp (workPair w₀ w₁))) 13
                  (fun _ _ => zfBAction_length _))
          simpa using h)
      simpa using h)
  simpa using h

/-- The table reader recovers every transition. Blank/false/true exhaust each
read alphabet; a two-work-tape read vector is determined by its two coordinates. -/
private lemma zfBReadTable_append (M : Code2TM) (xs : List Bool) :
    codeReadVec (codeReadSymbols (codeReadSymbols (codeReadSymbols (zfBReadAction M.numStates))))
      (M.numStates + 1)
      (((List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w₀ =>
            ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
              actionBits₂ (M.tm.tr q inp (workPair w₀ w₁))) ++ xs) =
      some ((fun q inp w₀ w₁ => M.tm.tr q inp (workPair w₀ w₁)), xs) :=
  codeReadVec_append _ _
    (fun _ _ => codeReadSymbols_append _ _
      (fun _ _ => codeReadSymbols_append _ _
        (fun _ _ => codeReadSymbols_append _ _ zfBReadAction_append _ _) _ _) _ _) _ _ _

/-- The complete parser recovers a serialized machine under arbitrary true padding.
**Proof sketch.** The doubled-bit parser first recovers the canonical state-count bits. The table length bound discharges the early guard; the field and vector inverse laws then recover the initial state and every transition. The remaining replicated true bits pass the suffix test. -/
private lemma zfBParse_serialize_pad (M : Code2TM) (m : ℕ) :
    zfBParse (M.serialize ++ List.replicate m true) = some M := by
  have hp (a b c : List Bool) : pairEncode a b ++ c = pairEncode a (b ++ c) := by
    simp [pairEncode, List.append_assoc]
  unfold Code2TM.serialize
  rw [hp]
  unfold zfBParse
  rw [pairDecode_pairEncode]
  dsimp only [bind, Option.bind]
  rw [codeBitsNat_bits]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  have hlen := zfBTable_length M
  simp only [List.length_append, List.length_replicate] at *
  rw [if_neg (by omega)]
  simp only [List.append_assoc, codeReadFin_append, zfBReadTable_append,
    List.all_replicate, id_eq, ite_self, ↓reduceIte, pure]
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
      fin_cases i <;> simp [workPair]

/-- The total decoder satisfies the required exact padded round-trip law. -/
private lemma zfBDecode_serialize_pad (M : Code2TM) (m : ℕ) :
    zfBDecode (M.serialize ++ List.replicate m true) = M := by
  simp only [zfBDecode, zfBParse_serialize_pad, Option.getD_some]

/-- Successful record parsing characterizes its complete serialized prefix.
**Proof sketch.** Decompose the seven successful reads, apply the dictionary
inverse to each, and concatenate their consumed prefixes in order. -/
private lemma zfBReadAction_sound {n : ℕ} (xs : List Bool)
    (a : Action 2 Bool (Fin (n + 1))) (rest : List Bool)
    (h : zfBReadAction n xs = some (a, rest)) : xs = actionBits₂ a ++ rest := by
  simp only [zfBReadAction, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨im, r₁⟩, h₁, ⟨⟨wr, r₂⟩, h₂, ⟨⟨wm, r₃⟩, h₃,
    ⟨⟨wr₁, r₄⟩, h₄, ⟨⟨wm₁, r₅⟩, h₅, ⟨⟨out, r₆⟩, h₆,
      ⟨⟨q, r₇⟩, h₇, h⟩⟩⟩⟩⟩⟩⟩ := h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rw [codeReadSign_sound xs im r₁ h₁, codeReadWrite_sound r₁ wr r₂ h₂,
    codeReadSign_sound r₂ wm r₃ h₃, codeReadWrite_sound r₃ wr₁ r₄ h₄,
    codeReadSign_sound r₄ wm₁ r₅ h₅, codeReadOutput_sound r₅ out r₆ h₆,
    codeReadState_sound r₆ q r₇ h₇]
  simp [actionBits₂, List.append_assoc]

/-- Skip one seven-field transition record, keeping only the unconsumed suffix. -/
private def zfBSkipAction (n : ℕ) (xs : List Bool) : Option (List Bool) := do
  let xs ← codeSkipPair (fun a b => a || !b) xs
  let xs ← codeSkipPair (fun _ _ => true) xs
  let xs ← codeSkipPair (fun a b => a || !b) xs
  let xs ← codeSkipPair (fun _ _ => true) xs
  let xs ← codeSkipPair (fun a b => a || !b) xs
  let xs ← codeSkipPair (fun a b => a || !b) xs
  codeSkipState (n + 1) xs


private lemma zfBEraseAction (n : ℕ) (xs : List Bool) :
    (zfBReadAction n xs).map Prod.snd = zfBSkipAction n xs := by
  simp only [zfBReadAction, zfBSkipAction, bind, Option.map_bind, Function.comp_def, pure, Option.map_some]
  rw [← codeEraseSign xs, ← codeErase_bind]
  congr 1; funext p
  rw [← codeEraseWrite p.2, ← codeErase_bind]
  congr 1; funext p
  rw [← codeEraseSign p.2, ← codeErase_bind]
  congr 1; funext p
  rw [← codeEraseWrite p.2, ← codeErase_bind]
  congr 1; funext p
  rw [← codeEraseSign p.2, ← codeErase_bind]
  congr 1; funext p
  rw [← codeEraseOutput p.2, ← codeErase_bind]
  congr 1; funext p
  simpa only [Option.map_eq_bind, Function.comp_def] using codeEraseState (n + 1) p.2

private def zfBParseFull (xs : List Bool) : Option (Code2TM × List Bool) := do
  let (bits, rest) ← pairDecode xs
  let n := codeBitsNat bits
  if bits ≠ n.bits then none else do
    if 351 * (n + 1) > rest.length then none else do
      let (q, rest) ← codeReadFin (n + 1) rest
      let (table, rest) ← codeReadVec
        (codeReadSymbols (codeReadSymbols (codeReadSymbols (zfBReadAction n)))) (n + 1) rest
      if rest.all id then
        pure (⟨n, ⟨q, fun s inp w => table s inp (w 0) (w 1)⟩⟩, rest)
      else none

/-- The erased parser: accept exactly the strings the parser accepts, returning only the unconsumed all-true suffix. -/
private def zfBScan (xs : List Bool) : Option (List Bool) := do
  let (bits, rest) ← pairDecode xs
  let n := codeBitsNat bits
  if bits ≠ n.bits then none else do
    if 351 * (n + 1) > rest.length then none else do
      let rest ← codeSkipFin (n + 1) rest
      let rest ← codeSkipRepeat (codeSkipRepeat (codeSkipRepeat (codeSkipRepeat (zfBSkipAction n) 3) 3) 3) (n + 1) rest
      if rest.all id then pure rest else none

private lemma zfBParse_full (xs : List Bool) : zfBParse xs = (zfBParseFull xs).map Prod.fst := by
  simp only [zfBParse, zfBParseFull, bind, Option.map_bind, Function.comp_def]
  congr 1
  funext p
  dsimp only
  split <;> try simp only [Option.map_none]
  split <;> try simp only [Option.map_none, Option.map_bind, Function.comp_def]
  congr 1; funext q
  congr 1; funext t
  dsimp only
  split <;> rfl

private lemma zfBScan_full (xs : List Bool) : zfBScan xs = (zfBParseFull xs).map Prod.snd := by
  simp only [zfBScan, zfBParseFull, bind, Option.map_bind, Function.comp_def]
  congr 1
  funext p
  dsimp only
  split <;> try simp only [Option.map_none]
  split <;> try simp only [Option.map_none, Option.map_bind, Function.comp_def]
  have h (q : Fin (codeBitsNat p.1 + 1) × List Bool)
      (t : (Fin (codeBitsNat p.1 + 1) → Option Bool → Option Bool → Option Bool → Action 2 Bool (Fin (codeBitsNat p.1 + 1))) × List Bool) :
      (if t.2.all id then some ((⟨codeBitsNat p.1, ⟨q.1, fun s inp w => t.1 s inp (w 0) (w 1)⟩⟩ : Code2TM), t.2) else none).map Prod.snd =
        (if t.2.all id then some t.2 else none) := by split <;> rfl
  simp only [pure, h]
  rw [← codeEraseFin _ _, ← codeErase_bind]
  congr 1; funext q
  have ht := codeEraseVec (codeReadSymbols (codeReadSymbols (codeReadSymbols (zfBReadAction (codeBitsNat p.1)))))
    (codeBitsNat p.1 + 1) q.2
  simp only [codeEraseSymbols, zfBEraseAction] at ht
  rw [← ht, ← codeErase_bind]

/-- **Proof sketch.** Use the same decomposition as parser soundness, retaining the exact unconsumed suffix. The field soundness equations and the canonical count check reconstruct the original input as the machine serialization followed by that suffix. -/
private lemma zfBParseFull_sound (xs : List Bool) (M : Code2TM) (tail : List Bool)
    (h : zfBParseFull xs = some (M, tail)) : xs = M.serialize ++ tail := by
  unfold zfBParseFull at h
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
            (fun _ _ _ => codeReadSymbols_sound _ _
              (fun _ _ _ => codeReadSymbols_sound _ _ zfBReadAction_sound _ _ _) _ _ _) _ _ _)
          _ _ _ _ ht
        dsimp only at htable
        rw [eq_pairEncode_of_pairDecode xs bits rest hp, codeReadFin_sound rest q r₁ hq, htable]
        simp only [Code2TM.serialize, pairEncode, List.append_assoc]
        congr 1
        exact congrArg (List.flatMap fun b : Bool => [b, b]) hb
      · contradiction

/-- The canonical serialization of the machine a string denotes: the consumed prefix on scanner success, the fallback machine's serialization otherwise. -/
private def zfBCanonical (xs : List Bool) : List Bool :=
  (zfBScan xs).casesOn zfBFallback.serialize fun tail => xs.take (xs.length - tail.length)

/-- The suffix scanner computes exactly the fixed serialization of the decoded machine. -/
private lemma zfBCanonical_eq (xs : List Bool) : zfBCanonical xs = (zfBDecode xs).serialize := by
  unfold zfBCanonical zfBDecode
  rw [zfBScan_full, zfBParse_full]
  cases h : zfBParseFull xs with
  | none => rfl
  | some p =>
    rcases p with ⟨M, tail⟩
    simp only [Option.map_some, Option.getD_some]
    rw [zfBParseFull_sound xs M tail h]
    simp



private lemma zfBPrimSkipAction : Primrec₂ zfBSkipAction := by
  unfold zfBSkipAction
  apply Primrec.option_bind ((codePrimSkipPair _).comp Primrec.snd)
  change Primrec _
  apply Primrec.option_bind ((codePrimSkipPair _).comp Primrec.snd)
  change Primrec _
  apply Primrec.option_bind ((codePrimSkipPair _).comp Primrec.snd)
  change Primrec _
  apply Primrec.option_bind ((codePrimSkipPair _).comp Primrec.snd)
  change Primrec _
  apply Primrec.option_bind ((codePrimSkipPair _).comp Primrec.snd)
  change Primrec _
  apply Primrec.option_bind ((codePrimSkipPair _).comp Primrec.snd)
  change Primrec _
  exact codePrimSkipState.comp (Primrec.succ.comp
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))))) Primrec.snd

/-- **Proof sketch.** Compose primitive recursive readers, comparisons, and fixed-count iterations in the exact order of the erased parser. The canonical-count check and minimum-length check surround the state and record scans. The final branch accepts precisely an all-true suffix. -/
private lemma zfBPrimScan : Primrec zfBScan := by
  unfold zfBScan
  apply Primrec.option_bind codePrimPair
  change Primrec _
  apply Primrec.ite ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
    (codePrimBits.comp (codePrimBitsNat.comp (Primrec.fst.comp Primrec.snd)))).not)
    (Primrec.const none)
  apply Primrec.ite (Primrec.nat_lt.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.nat_mul.comp (Primrec.const 351) (Primrec.succ.comp (codePrimBitsNat.comp (Primrec.fst.comp Primrec.snd)))))
    (Primrec.const none)
  apply Primrec.option_bind (codePrimSkipFin.comp
    (Primrec.succ.comp (codePrimBitsNat.comp (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp Primrec.snd))
  change Primrec _
  have hr := codePrimRepeat _ (codePrimRepeat _ (codePrimRepeat _ (codePrimRepeat _ zfBPrimSkipAction (fun _ => 3) (Primrec.const 3))
    (fun _ => 3) (Primrec.const 3))
    (fun _ => 3) (Primrec.const 3)) (fun n => n + 1) Primrec.succ
  apply Primrec.option_bind (hr.comp
    (codePrimBitsNat.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)
  change Primrec _
  exact Primrec.ite (Primrec.eq.comp (codePrimAll.comp Primrec.snd) (Primrec.const true))
    (Primrec.option_some.comp Primrec.snd) (Primrec.const none)

private lemma zfBPrimCanonical : Primrec zfBCanonical :=
  Primrec.option_casesOn zfBPrimScan (Primrec.const zfBFallback.serialize)
    (codePrimPrefix.comp Primrec.fst (Primrec.list_length.comp Primrec.snd))



/-- **An effective two-tape code scheme exists** (spec, fill pending —
tranche A-S2).

**Proof sketch.** Mirror the received constructions over the
single-branch table: `encode := Code2TM.serialize` itself; `decode`
parses the `Turing.pairEncode`d state count, the initial state, and the
transition table by the received parser architecture
(`TCSlib.Complexity.TuringMachine.CodeParser`, retargeted to the
`Turing.actionBits₂` record at **27 records per state** — the
nondeterministic retarget's `2 · 27 = 54` without the choice bit, so its
minimum-length guard scales by exactly half), with the single-state
do-nothing machine as the fallback on parse failure and trailing
`true`-padding tolerated by the end-marker discipline (property 2); the
canonizer re-serializes the parsed record by the arbitrary-time
computability route of the received deterministic construction
(`TCSlib.Complexity.TuringMachine.MathlibBridge`), so no polynomial
canonizer is claimed. Fill obligations, named: the record parser and its
fallback totalization; the pad-tolerance lemma; the canonizer assembly
and its time bound.

**ZF-B implementation appendix.** The private seven-field parser and its
suffix scanner implement this route, including the up-front 351-per-state
length guard. The scanner-based canonizer is proved primitive recursive,
then compiled by the public `codePrim_machine` theorem. Its arbitrary
length-only time bound is supplied by that theorem. The private parser and
primitive-recursion adaptations are itemized in the delivery's duplication
ledger; no ND existence theorem is used. -/
theorem exists_effectiveMachineCode2 : Nonempty EffectiveMachineCode2 := by
  obtain ⟨M, T, h⟩ := codePrim_machine zfBCanonical zfBPrimCanonical
  refine ⟨{
    encode := Code2TM.serialize
    decode := zfBDecode
    decode_encode_pad := zfBDecode_serialize_pad
    canonizer := M
    canonizerTime := T
    canonizer_computes := ?_ }⟩
  simpa only [show zfBCanonical = fun xs => (zfBDecode xs).serialize from
    funext zfBCanonical_eq] using h

/-- A *uniformly timed* scheme for two-tape codes: the effective scheme
together with a bounded-acceptance simulator whose budget is one
polynomial **jointly** in the code length, input length, and time bound —
the mirror of `UniformMachineCode` (`Diagonalization/EXPCOM.lean`), which
exists because `EffectiveMachineCode2` deliberately bounds no decoding
time (the P3.2 lesson: with an arbitrary scheme, a variable-code consumer
can be made to pay unboundedly for decoding). -/
structure UniformMachineCode2 extends EffectiveMachineCode2 where
  /-- the uniformly timed bounded-acceptance simulator -/
  simulator : FinTM Bool
  /-- the simulator's single polynomial degree and coefficient -/
  simDegree : ℕ
  /-- on bounded acceptance, the simulator answers `[true]` within the
  uniform polynomial budget -/
  simulator_accepts : ∀ (α x : List Bool) (t : ℕ),
    (decode α).toFinTM.ComputesInTime x [true] t →
    simulator.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
      (simDegree * (α.length + x.length + t + 1) ^ simDegree)
  /-- otherwise it answers `[false]` within the same budget -/
  simulator_rejects : ∀ (α x : List Bool) (t : ℕ),
    ¬(decode α).toFinTM.ComputesInTime x [true] t →
    simulator.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
      (simDegree * (α.length + x.length + t + 1) ^ simDegree)

/-- **A uniformly timed two-tape scheme exists** (spec, fill pending —
tranche A-S2).

**Proof sketch.** The concrete scheme of
`Turing.exists_effectiveMachineCode2` with the uniform simulator built as
in the received `exists_uniformMachineCode` route
(`Diagonalization/EXPCOM.lean`, P3.2 round 2): parse the nested input
keeping the deadline in binary; check the table's minimum-length guard by
binary arithmetic before any per-state iteration (a huge declared state
count is never expanded in unary; the guard constant halves against the
nondeterministic table); then run the clocked step-by-step simulation of
the decoded two-tape machine, charging one uniform polynomial jointly in
`|α| + |x| + t + 1`. The two-work-tape simulation is *easier* than the
received one-tape case for the step itself (the simulator hosts the two
coded tapes on two physical tapes — no tape reduction), and the Z1
virtual-input layer supplies the input discipline. -/
theorem exists_uniformMachineCode2 : Nonempty UniformMachineCode2 := by
  sorry

end Turing
