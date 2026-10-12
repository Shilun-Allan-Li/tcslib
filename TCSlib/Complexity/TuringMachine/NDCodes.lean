/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.CodeFormat
import TCSlib.Complexity.TuringMachine.Nondeterministic
import TCSlib.Complexity.TuringMachine.MathlibBridge

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Codes for nondeterministic machines

The nondeterministic counterpart of `TCSlib.Complexity.TuringMachine.Encoding`'s
code layer ([AB09, §1.4], extended to NDTMs as [AB09, §3.2] requires for the
nondeterministic time hierarchy): a coded normal form `Turing.CodeNDTM`, its
fixed scheme-independent serialization, the representation-scheme laws
(`Turing.NDMachineCode`), and the effective form with a canonizer
(`Turing.EffectiveNDMachineCode`). Phase P3.3 of
`AroraBarakChapters3-4Plan.md`; the consumers — the clocked universal NDTM of
[AB09, Exercise 2.6] at linear overhead (decision CH34-Q8) and the lazy
diagonalization of [AB09, Theorem 3.2] — are
`TCSlib.Complexity.Diagonalization.NTimeHierarchy`.

**Status: proved (phase P3.3).** The effective scheme existence and the
padded round-trip law are proved. The canonizer has an arbitrary length-only
time bound, as required by the audited contract.

## Design

* **The coded normal form has two work tapes** (`NDTM 2 Bool`), not one: the
  deterministic `Turing.CodeTM` is one-work-tape because the chapter-1
  robustness conversion eats a quadratic slowdown anyway, but phase P3.3's
  whole point (decision CH34-Q8) is **linear** overhead, and the
  guess-then-verify tape reduction ([BGW70]-style, stated as
  `Turing.FinNDTM.exists_codeNDTM_accepts_linear` in the consumer module)
  delivers linear overhead into **two** work tapes — one for the guessed
  display sequence, one replaying the verified tape — while the one-work-tape
  target is not known to suffice at linear cost.
* **The serialization mirrors `Turing.CodeTM.serialize` record for record**:
  the same `signBits`/`optOptBoolBits`/`optBoolBits`/`optStateBits` fields,
  with a second work-tape record per action (`Turing.actionBits₂`) and the
  table enumerated over the choice bit first (`false` then `true`), then
  states in `Fin` order, then the input read and the two work reads each over
  `none`, `some false`, `some true`.
* **The scheme laws are verbatim mirrors**: total decoding (property 1),
  recovery under arbitrary `true`-padding (property 2 — infinitely many
  representations, which [AB09, Theorem 3.2]'s proof uses to pick a large
  index), and the canonizer tying `decode` to effective semantics (the
  chapter-1 audit's Argument-A exclusion, inherited by construction).

## Main definitions

* `Turing.CodeNDTM`, `Turing.CodeNDTM.toFinNDTM` — the coded two-work-tape
  normal form. [AB09, §1.4, §3.2]
* `Turing.actionBits₂`, `Turing.CodeNDTM.serialize` — the fixed serialization.
* `Turing.NDMachineCode`, `Turing.EffectiveNDMachineCode` — the scheme laws
  and the effective scheme. [AB09, §1.4]

## Main results

* `Turing.NDMachineCode.decode_encode` — decoding recovers the machine
  (skeleton-time proof, mirror of `Turing.MachineCode.decode_encode`).
* `Turing.exists_effectiveNDMachineCode` — an effective scheme exists
  (proved; phase P3.3).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, §2.1.2, Exercise 2.6; §3.2.)
* [BGW70] R. Book, S. Greibach, B. Wegbreit, *Time- and tape-bounded Turing
  acceptors and AFLs*, JCSS 4(6), 1970. (Cited through [AB09]; no external
  text is required for this audit.)

## Item-8 appendix

The fixed `workPair` and `actionBits₂` definitions now live verbatim in
`CodeFormat`. The nondeterministic format instance remains a later fill obligation.

**Fill appendix.** The item-8 obligation above is now discharged by the private
`ndFormat` instance: two consecutive two-work-tape tables, false choice first,
with guard 702. The shared format decoder supplies padding tolerance and
`CodeFormat.exists_canonizer` supplies the arbitrary-time canonizer.
-/

namespace Turing

/-- The coded normal form of a nondeterministic machine: a binary-alphabet
NDTM with **two** work tapes and state space `Fin (numStates + 1)` (never
empty). Two work tapes, not one, because the guess-then-verify tape reduction
achieves linear overhead into two tapes (see the module docstring). Mirrors
`Turing.CodeTM`. [AB09, §1.4, §3.2] -/
structure CodeNDTM where
  /-- one less than the number of states (so the state space is never empty) -/
  numStates : ℕ
  /-- the underlying two-work-tape nondeterministic machine -/
  tm : NDTM 2 Bool (Fin (numStates + 1))

/-- The bundled machine of a coded nondeterministic machine. -/
def CodeNDTM.toFinNDTM (M : CodeNDTM) : FinNDTM Bool where
  k := 2
  State := Fin (M.numStates + 1)
  tm := M.tm

/-- The **fixed, scheme-independent** canonical serialization of a coded
nondeterministic machine, mirroring `Turing.CodeTM.serialize`: the state count,
the initial state, then the full two-table transition list in the fixed
enumeration order — the choice bit (`false` then `true`) outermost, then
states in `Fin` order, then the input read and the two work reads each over
`none`, `some false`, `some true`. This is the target format of
`Turing.EffectiveNDMachineCode.canonizer`. -/
def CodeNDTM.serialize (M : CodeNDTM) : List Bool :=
  pairEncode (Nat.bits M.numStates)
    (unaryFin M.tm.q₀ ++
      ([false, true] : List Bool).flatMap fun b =>
        (List.finRange (M.numStates + 1)).flatMap fun q =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
            ([none, some false, some true] : List (Option Bool)).flatMap fun w₀ =>
              ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
                actionBits₂ (M.tm.tr b q inp (workPair w₀ w₁)))

/-- The algebraic laws of a representation scheme for coded nondeterministic
machines, mirroring `Turing.MachineCode` [AB09, §1.4]: a total decoding
(property 1), an encoding, and recovery under arbitrary `true`-padding
(property 2 — every machine has infinitely many representations, which the
lazy diagonalization of [AB09, Theorem 3.2] uses to pick large indices). -/
structure NDMachineCode where
  /-- encode a machine as a binary string, `⌞N⌟` -/
  encode : CodeNDTM → List Bool
  /-- decode any binary string to a machine (total by type: property 1) -/
  decode : List Bool → CodeNDTM
  /-- a code followed by any amount of `true`-padding decodes to the machine
  (property 2: infinitely many representations) -/
  decode_encode_pad : ∀ M m, decode (encode M ++ List.replicate m true) = M

/-- Decoding a code recovers the machine ([AB09, §1.4]; padding by zero
symbols). Skeleton-time proof, mirroring `Turing.MachineCode.decode_encode`. -/
theorem NDMachineCode.decode_encode (c : NDMachineCode) (M : CodeNDTM) :
    c.decode (c.encode M) = M := by
  simpa using c.decode_encode_pad M 0

/-- An *effective* representation scheme for nondeterministic machines: the
algebraic laws together with a (deterministic) machine of this development
computing the fixed serialization of the decoded machine — the mirror of
`Turing.EffectiveMachineCode`, with the same Argument-A rationale: the target
`Turing.CodeNDTM.serialize` is scheme-independent, so a scheme whose `decode`
has noncomputable meaning admits no canonizer. -/
structure EffectiveNDMachineCode extends NDMachineCode where
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's time bound (arbitrary here; universal-machine constants
  absorb its value at each fixed code) -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serialize ∘ decode` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => (decode α).serialize) canonizerTime

/-- The nondeterministic code format consists of the false-choice and true-choice
two-work-tape tables, in that order, with a silent one-state fallback. [AB09, §1.4, §3.2]

**Proof sketch.** Assemble the two tables by inspecting the choice bit and the
two work reads. Every work-read function is recovered from its two coordinates.
The shared table reader's inverse, soundness and erasure laws compose twice;
adding its two 351-bit lower bounds gives the 702-bit guard. -/
private def ndFormat : CodeFormat where
  Code := CodeNDTM
  Table := fun n => CodeTable2 n × CodeTable2 n
  numStates := CodeNDTM.numStates
  assemble := fun n q t => ⟨n, ⟨q, fun b s inp w =>
    (if b then t.2 else t.1) s inp (w 0) (w 1)⟩⟩
  serialize := CodeNDTM.serialize
  tableBits := fun t => codeTable2Bits t.1 ++ codeTable2Bits t.2
  readTable := fun n xs => do
    let (t₀, xs) ← codeReadTable2 n xs
    let (t₁, xs) ← codeReadTable2 n xs
    pure ((t₀, t₁), xs)
  skipTable := fun n => codeSkipRepeat (codeSkipTable2 n) 2
  guard := 702
  fallback := ⟨0, ⟨0, fun _ _ _ _ =>
    ⟨.zero, fun _ => (none, .zero), none, none⟩⟩⟩
  numStates_assemble := fun _ _ _ => rfl
  serialize_assemble := fun _ _ _ => by
    simp [CodeNDTM.serialize, codeTable2Bits, actionBits₂_eq_actionBitsK, workPair]
  assemble_surj := by
    rintro ⟨n, q, tr⟩
    refine ⟨n, q, (fun s inp w₀ w₁ => tr false s inp (workPair w₀ w₁),
      fun s inp w₀ w₁ => tr true s inp (workPair w₀ w₁)), ?_⟩
    congr 1
    congr 1
    funext b s inp w
    have hw : workPair (w 0) (w 1) = w := by
      funext j
      by_cases hj : j = 0
      · simp [workPair, hj]
      · have hj' : j = 1 := Fin.ext (by omega)
        simp [workPair, hj']
    cases b <;> simp [hw]
  readTable_append := by
    intro n t xs
    simp only [List.append_assoc, codeReadTable2_append, bind, Option.bind_some, pure]
  readTable_sound := by
    intro n xs t rest h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨t₀, r₀⟩, h₀, ⟨⟨t₁, r₁⟩, h₁, h⟩⟩ := h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rw [codeReadTable2_sound xs t₀ r₀ h₀, codeReadTable2_sound r₀ t₁ r₁ h₁,
      List.append_assoc]
  readTable_erase := by
    intro n xs
    simp only [bind, Option.map_bind, Function.comp_def, pure, Option.map_some,
      codeSkipRepeat, Option.bind_fun_some]
    rw [← codeEraseTable2 n xs, ← codeErase_bind]
    congr 1
    funext p
    simpa only [Option.map_eq_bind, Function.comp_def] using codeEraseTable2 n p.2
  tableBits_length := by
    intro n t
    have h₀ := codeTable2Bits_length t.1
    have h₁ := codeTable2Bits_length t.2
    simp only [List.length_append]
    omega

/-- **An effective nondeterministic code scheme exists** (proved —
phase P3.3): the mirror of `Turing.exists_effectiveMachineCode`.

**Proof sketch.** Mirror the deterministic construction
(`TCSlib.Complexity.TuringMachine.MathlibBridge`) over the extended record
format: `encode := CodeNDTM.serialize` itself; `decode` parses the
`Turing.pairEncode`d state count, the initial state, and the two transition
tables by the received parser architecture
(`TCSlib.Complexity.TuringMachine.CodeParser`, retargeted to the
`Turing.actionBits₂` record — the table is `2 · 27 = 54` records per state
in the fixed enumeration order, two choices by three reads on each of the
input and both work tapes; round-1 finding 3 corrected the earlier `2 · 9`
miscount, and the parser's minimum-length guard scales accordingly), with
the single-state do-nothing machine as the fallback on parse failure and
trailing `true`-padding tolerated by the end-marker discipline
(property 2); the canonizer re-serializes the parsed record by the
**arbitrary-time computability route of the received construction** — the
deterministic `MathlibBridge` explicitly supersedes its polynomial variant,
and `canonizerTime` is an arbitrary bound, so no polynomial ND canonizer is
claimed or needed by this phase's consumers (round-1 finding 4). Fill obligations, named: the record parser and its fallback
totalization; the pad-tolerance lemma (`decode_encode_pad`); the canonizer
assembly and its time bound.

**Fill appendix.** The retargeted parser in the sketch is the shared
`CodeFormat` decoder instantiated by `ndFormat`; no separate parser is needed.
Its table skipper repeats `codeSkipTable2` twice, so `codePrimRepeat` and
`codePrimSkipTable2` establish primitive recursiveness. Apply
`CodeFormat.decode_serialize_pad` for recovery and
`CodeFormat.exists_canonizer` for the deterministic canonizer and its
arbitrary time bound. -/
theorem exists_effectiveNDMachineCode : Nonempty EffectiveNDMachineCode := by
  have hskip : Primrec₂ ndFormat.skipTable :=
    codePrimRepeat codeSkipTable2 codePrimSkipTable2 (fun _ => 2) (Primrec.const 2)
  obtain ⟨canonizer, time, hcanonizer⟩ := ndFormat.exists_canonizer hskip
  exact ⟨{
    encode := CodeNDTM.serialize
    decode := ndFormat.decode
    decode_encode_pad := ndFormat.decode_serialize_pad
    canonizer := canonizer
    canonizerTime := time
    canonizer_computes := hcanonizer }⟩

end Turing
