/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.TuringMachine.MathlibBridge
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.TuringMachine.Build.VirtualInput
import TCSlib.Complexity.TuringMachine.Build.Catalog

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

## Item-8 appendix

The two-work-tape parser and canonizer now instantiate the shared `CodeFormat`
layer. ZF-B3 consumes its decoded-size and guard corollaries, with the existing
silent fallback and every public scheme statement preserved.
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

The fixed silent fallback and the two-work-tape instance of `CodeFormat` supply
this format's parser and canonizer. The common record, table and primitive-recursion
laws live in `CodeFormat` and `MathlibBridge`; `zfBDecode` remains a typed alias
for the frozen uniform-simulator statements.
-/



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

/-- The deterministic two-work-tape code format, with 27 records per state
and the fixed silent fallback. [AB09, §1.4] -/
private def twoTapeFormat : CodeFormat where
  Code := Code2TM
  Table := CodeTable2
  numStates := Code2TM.numStates
  assemble := fun n q t => ⟨n, ⟨q, fun s inp w => t s inp (w 0) (w 1)⟩⟩
  serialize := Code2TM.serialize
  tableBits := fun t => codeTable2Bits t
  readTable := codeReadTable2
  skipTable := codeSkipTable2
  guard := 351
  fallback := zfBFallback
  numStates_assemble := fun _ _ _ => rfl
  serialize_assemble := fun _ _ _ => by
    simp [Code2TM.serialize, codeTable2Bits, actionBits₂_eq_actionBitsK, workPair]
  assemble_surj := by
    rintro ⟨n, q, tr⟩
    refine ⟨n, q, fun s inp w₀ w₁ => tr s inp (workPair w₀ w₁), ?_⟩
    show Code2TM.mk n ⟨q, fun s inp w => tr s inp (workPair (w 0) (w 1))⟩ = Code2TM.mk n ⟨q, tr⟩
    congr 1
    congr 1
    funext s inp w
    apply congrArg (tr s inp)
    funext i
    fin_cases i <;> simp [workPair]
  readTable_append := fun _ t xs => codeReadTable2_append t xs
  readTable_sound := fun _ xs t rest h => codeReadTable2_sound xs t rest h
  readTable_erase := codeEraseTable2
  tableBits_length := fun _ t => codeTable2Bits_length t

/-- Total decoding: every malformed string denotes the fixed fallback. -/
private def zfBDecode (xs : List Bool) : Code2TM := twoTapeFormat.decode xs

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
ledger; no ND existence theorem is used. 

**Item-8 appendix.** The two-work-tape instance now consumes the shared
`CodeFormat` parser, padded round trip and canonizer construction. The 351-per-state
guard and fixed fallback are unchanged; the private parser copies are removed. -/
theorem exists_effectiveMachineCode2 : Nonempty EffectiveMachineCode2 := by
  obtain ⟨M, T, h⟩ := twoTapeFormat.exists_canonizer codePrimSkipTable2
  exact ⟨⟨⟨Code2TM.serialize, zfBDecode, twoTapeFormat.decode_serialize_pad⟩, M, T, h⟩⟩

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

/-! ### Uniform-simulator preparation (ZF-B3)

The two added Build imports are sanctioned by the B3 brief. The following
facts concern the concrete decoder, the finite output summary, and a real
deadline test assembled from public machines. They do not assert a running
time for the primitive-recursive canonizer or implement the table interpreter.
-/

/-- The decoded table is no longer than the code, except for the fixed
354-bit fallback. This bounds stored data, not the canonizer's running time.

**Proof sketch.** Cite the scanner/canonizer equality. A successful scan
selects a prefix of the input; an unsuccessful scan selects the fallback. -/
private lemma zfB3_decode_length (α : List Bool) :
    (zfBDecode α).serialize.length ≤ max α.length 354 := by
  have h := twoTapeFormat.serialize_decode_length_le α
  change (zfBDecode α).serialize.length ≤ max α.length zfBFallback.serialize.length at h
  rwa [zfBFallback_serialize_length] at h

/-- The decoded state table has a linear size bound, including malformed
codes. The table guard is used before its state-indexed reader is evaluated. -/
private lemma zfB3_decode_states (α : List Bool) :
    351 * ((zfBDecode α).numStates + 1) ≤ max α.length 354 := by
  have h := twoTapeFormat.numStates_decode_le α
  change 351 * ((zfBDecode α).numStates + 1) ≤
    max α.length zfBFallback.serialize.length at h
  rwa [zfBFallback_serialize_length] at h

/-- A failed lower-length guard chooses the fallback without invoking the
initial-state or transition-table readers, even for an enormous binary count. -/
private lemma zfB3_guard_failure (α bits rest : List Bool)
    (hp : pairDecode α = some (bits, rest))
    (hg : rest.length < 351 * (codeBitsNat bits + 1)) :
    zfBDecode α = zfBFallback :=
  twoTapeFormat.decode_of_guard_lt α bits rest hp hg

/-- Output summary: `none` means empty, `some true` means exactly `[true]`,
and `some false` means any other output. The last class is irreversible. -/
private def zfB3Output : List Bool → Option Bool
  | [] => none
  | [true] => some true
  | _ => some false

/-- Update the three-way summary for the emission of one source transition. -/
private def zfB3Emit : Option Bool → Option Bool → Option Bool
  | s, none => s
  | none, some true => some true
  | _, some _ => some false

/-- Summary update accounts for the symbol on a halting transition as well. -/
private lemma zfB3Output_append (w : List Bool) (b : Option Bool) :
    zfB3Output (w ++ b.toList) = zfB3Emit (zfB3Output w) b := by
  cases b with
  | none => simp [zfB3Emit]
  | some b =>
    cases w with
    | nil => cases b <;> rfl
    | cons a w =>
      cases w with
      | nil => cases a <;> cases b <;> rfl
      | cons c w => cases a <;> cases b <;> rfl

/-- The summary's accepting value characterizes the exact singleton output. -/
private lemma zfB3Output_true (w : List Bool) :
    zfB3Output w = some true ↔ w = [true] := by
  cases w with
  | nil => simp [zfB3Output]
  | cons b w =>
    cases w with
    | nil => cases b <;> simp [zfB3Output]
    | cons c w => cases b <;> simp [zfB3Output]

/-- Once the summary is other, no subsequent emission can repair it. -/
private lemma zfB3Emit_other (b : Option Bool) :
    zfB3Emit (some false) b = some false := by
  cases b with
  | none => rfl
  | some b => cases b <;> rfl

/-- Semantic clock for the two-tape simulator. It performs exactly the
permitted number of source steps, maintaining only the finite output summary,
and then inspects halting and exact output. This is a specification function,
not a finite-machine construction or a claim about machine time. -/
private def zfB3Clock (M : Code2TM) {x : List Bool} :
    ℕ → Cfg 2 Bool (Fin (M.numStates + 1)) x → Option Bool → Bool
  | 0, c, s => c.state.isNone && (s == some true)
  | t + 1, c, s =>
    zfB3Clock M t (M.tm.step c) (zfB3Emit s (M.tm.outputSymbol c))

/-- The clock's final inspection includes the last permitted transition.
Halted configurations are allowed, so the equation also covers padding an
early halt to the deadline.

**Proof sketch.** Induct on the deadline. The output-summary update is
exactly append by the step's optional emission; cite the public run and
output-step equations to identify the residual run. -/
private lemma zfB3Clock_correct (M : Code2TM) {x : List Bool}
    (c : Cfg 2 Bool (Fin (M.numStates + 1)) x) (t : ℕ) :
    zfB3Clock M t c (zfB3Output c.output) =
      ((M.tm.runFrom c t).state.isNone &&
        (zfB3Output (M.tm.runFrom c t).output == some true)) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    rw [zfB3Clock, ← zfB3Output_append, ← MultiTapeTM.step_output, ih]
    rw [MultiTapeTM.runFrom_succ_eq_step]

/-- Bounded acceptance for the concrete decoder, with the three-way summary.
The deadline here is a semantic natural number; the implementation must keep
its representation in binary. -/
private def zfB3Answer (α x : List Bool) (t : ℕ) : Bool :=
  zfB3Clock (zfBDecode α) t ((zfBDecode α).tm.initCfg x) none

/-- Both answer branches have the exact frozen bounded-acceptance meaning. -/
private lemma zfB3Answer_correct (α x : List Bool) (t : ℕ) :
    zfB3Answer α x t = true ↔
      (zfBDecode α).toFinTM.ComputesInTime x [true] t := by
  unfold zfB3Answer
  change zfB3Clock (zfBDecode α) t ((zfBDecode α).tm.initCfg x)
    (zfB3Output ((zfBDecode α).tm.initCfg x).output) = true ↔ _
  rw [zfB3Clock_correct, FinTM.computesInTime_iff]
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq,
    zfB3Output_true, Code2TM.toFinTM]

/-- Deadline zero rejects by the public source-side zero-time impossibility. -/
private lemma zfB3Answer_zero (α x : List Bool) : zfB3Answer α x 0 = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact FinTM.not_computesInTime_zero (zfBDecode α).toFinTM x [true]
    ((zfB3Answer_correct α x 0).mp h)

/-- Any malformed code selects a silent fallback and hence rejects at every
deadline, including zero. No simulation of a putative huge table is needed.

**Proof sketch.** At zero cite the public impossibility theorem. At a
positive deadline the fallback halts silently on its first transition;
the public absorbing-halt equation preserves its empty output thereafter. -/
private lemma zfB3Answer_malformed (α x : List Bool) (t : ℕ)
    (hparse : twoTapeFormat.parseFull α = none) : zfB3Answer α x t = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  have h := (zfB3Answer_correct α x t).mp ht
  have hd : zfBDecode α = zfBFallback :=
    twoTapeFormat.decode_of_parseFull_none α hparse
  rw [hd] at h
  cases t with
  | zero => exact FinTM.not_computesInTime_zero _ _ _ h
  | succ t =>
    have hout := ((FinTM.computesInTime_iff _ _ _ _).mp h).2
    change (zfBFallback.tm.runFrom (zfBFallback.tm.initCfg x) (t + 1)).output =
      [true] at hout
    have hh : (zfBFallback.tm.step (zfBFallback.tm.initCfg x)).state = none := rfl
    rw [MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_of_halt _ hh] at hout
    contradiction

/-- One real finite machine tests whether the nested binary deadline is positive in a
linear joint budget. It does not expand the deadline or enumerate states.

**Proof sketch.** Extract the first component twice by the public catalog
row, then use the public empty-word comparator. Compose with the pointwise
time theorem, so the cost is charged to these particular intermediate words.
The pairing length identity and `length_bits_le_self` give the joint bound.
It returns `[false]` at deadline zero and a continuation flag at positive
deadlines. The continuation flag is not an acceptance verdict. -/
private lemma zfB3_deadline_test :
    ∃ (D : FinTM Bool) (c : ℕ), ∀ (α x : List Bool) (t : ℕ),
      D.ComputesInTime (pairEncode (pairEncode t.bits α) x) [decide (t ≠ 0)]
        (c * (α.length + x.length + t + 1)) := by
  obtain ⟨F, a, hF, _⟩ := FinTM.computesFunInTime_pairFst_spaceUsed
  obtain ⟨E, b, hE⟩ := FinTM.computesFunInTime_ifEq [] [false] [true]
  refine ⟨FinTM.bufferedCompTM (FinTM.bufferedCompTM F F) E,
    10 * a + b + 6, ?_⟩
  intro α x t
  have h₁ := hF (pairEncode (pairEncode t.bits α) x)
  have h₂ := hF (pairEncode t.bits α)
  simp only [pairDecode_pairEncode, Option.map_some, Option.getD_some] at h₁ h₂
  have h₃ := FinTM.bufferedCompTM_computesInTime F F h₁ h₂
  have h₄ := hE t.bits
  have hout : (if t.bits = [] then [false] else [true]) = [decide (t ≠ 0)] := by
    have hz : t.bits = [] ↔ t = 0 := by
      constructor
      · intro h
        have hvalue := codeBitsNat_bits t
        rw [h] at hvalue
        exact hvalue.symm
      · intro h
        simp [h]
    simp only [hz]
    by_cases h : t = 0 <;> simp [h]
  dsimp only at h₄
  rw [hout] at h₄
  apply (FinTM.bufferedCompTM_computesInTime (FinTM.bufferedCompTM F F) E h₃ h₄).mono
  let N := α.length + x.length + t + 1
  have hbits := length_bits_le_self t
  have hi : (pairEncode (pairEncode t.bits α) x).length + 1 ≤ 7 * N := by
    simp only [length_pairEncode]
    dsimp only [N]
    omega
  have hp : (pairEncode t.bits α).length + 1 ≤ 3 * N := by
    simp only [length_pairEncode]
    dsimp only [N]
    omega
  have ht : t.bits.length + 1 ≤ N := by dsimp only [N]; omega
  have hbridge₁ : (pairEncode t.bits α).length + 2 ≤ 4 * N := by
    simp only [length_pairEncode]
    dsimp only [N]
    omega
  have hbridge₂ : t.bits.length + 2 ≤ 2 * N := by dsimp only [N]; omega
  have ha₁ : a * ((pairEncode (pairEncode t.bits α) x).length + 1) ≤ 7 * (a * N) :=
    (Nat.mul_le_mul_left a hi).trans_eq (by ac_rfl)
  have ha₂ : a * ((pairEncode t.bits α).length + 1) ≤ 3 * (a * N) :=
    (Nat.mul_le_mul_left a hp).trans_eq (by ac_rfl)
  have hb : b * (t.bits.length + 1) ≤ b * N := Nat.mul_le_mul_left b ht
  change _ ≤ (10 * a + b + 6) * N
  simp only [Nat.add_mul, Nat.mul_assoc]
  omega

/-- A concrete simulator with one joint monomial bound suffices for the
frozen uniform scheme. Both verdicts use the same degree and coefficient.

**Proof sketch.** Assemble the same concrete effective scheme with the
public primitive-recursive canonizer theorem. Increase the simulator's
coefficient and exponent together to `C + e + 1`; the joint size is positive.
The clock correctness equation supplies both complementary verdicts. This
lemma is conditional: its simulator hypothesis is the remaining construction
obligation, not an arbitrary-time compiler conclusion. -/
private lemma zfB3_uniform_of_simulator (S : FinTM Bool) (C e : ℕ)
    (hS : ∀ (α x : List Bool) (t : ℕ),
      S.ComputesInTime (pairEncode (pairEncode t.bits α) x) [zfB3Answer α x t]
        (C * (α.length + x.length + t + 1) ^ e)) :
    Nonempty UniformMachineCode2 := by
  obtain ⟨M, T, hM⟩ := twoTapeFormat.exists_canonizer codePrimSkipTable2
  have hbound (α x : List Bool) (t : ℕ) :
      C * (α.length + x.length + t + 1) ^ e ≤
        (C + e + 1) * (α.length + x.length + t + 1) ^ (C + e + 1) :=
    Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right (by omega) (by omega))
  refine ⟨{
    encode := Code2TM.serialize
    decode := zfBDecode
    decode_encode_pad := twoTapeFormat.decode_serialize_pad
    canonizer := M
    canonizerTime := T
    canonizer_computes := ?_
    simulator := S
    simDegree := C + e + 1
    simulator_accepts := ?_
    simulator_rejects := ?_ }⟩
  · exact hM
  · intro α x t h
    have ha := (zfB3Answer_correct α x t).mpr h
    simpa only [ha] using (hS α x t).mono (hbound α x t)
  · intro α x t h
    have ha : zfB3Answer α x t = false :=
      Bool.eq_false_iff.mpr (fun ht => h ((zfB3Answer_correct α x t).mp ht))
    simpa only [ha] using (hS α x t).mono (hbound α x t)

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
