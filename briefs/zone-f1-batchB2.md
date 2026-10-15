# §13 fill campaign — Tranche A-S2, Batch ZF-B2 (continuation): the two-tape code schemes (`Codes2Tape.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch,
  NOT `main`.
- Create your working branch off it (suggested name `fill/zone-f1-B2`).
  Record the base commit hash in `REPORT.md`; the brief was issued at
  `f171767f32e573c345f3fa9b6e9fb87e14b84ddf`. Never rebase.
- **Delivery is by zip, not PR or push**: `zone-f1-B2.zip` with the
  standard contents (report, full source, format-patch series, bundle,
  sweep log, axiom log, `SHA256SUMS`).

## What this is

This is a continuation of batch ZF-B (`briefs/zone-f1-batchB.md`; read it
in full, since everything there binds unless amended here). ZF-B proved
**target 1**, `Turing.exists_effectiveMachineCode2`. **69 of its 70 new
private helpers, however, were local copies or adaptations** of private
material in `CodeParser.lean` and `MathlibBridge.lean`, which it could not
cite. Its report is `audits/zone-agent-reports/f1-B-REPORT.md`, with every
copy itemized. **The delivery was not integrated.**

**User decision (2026-10-10): promote first.** At the issue base, the
maintainer made the **46 format-independent originals public**, statements
unchanged and with docstrings added:

- `CodeParser.lean` (33): `codeReadUnary_append`, `codeReadFin`, `codeReadSign`,
  `codeReadOutput`, `codeReadWrite`, `codeReadState`, `codeReadSymbols`,
  `codeReadVec`; the `_append` and `_sound` laws of `Fin`/`Sign`/`Output`/
  `Write`/`State`/`Symbols`/`Vec` (plus `codeReadUnary_sound`);
  `codeBitsNat_bits`, `codeFlatMap_length`; `codeEraseFin`, `codeEraseSign`,
  `codeEraseOutput`, `codeEraseWrite`, `codeEraseState`, `codeErase_bind`,
  `codeEraseSymbols`, `codeEraseVec`.
- `MathlibBridge.lean` (13): `codePrimUnary`, `codePrimBit`, `codePrimBitsNat`,
  `codePrimPair`, `codePrimBits`, `codePrimSkipPair`, `codePrimSkipFin`,
  `codePrimSkipState`, `codeSkipRepeat_iter`, `codePrimRepeat`, `codePrimAll`,
  `codePrimDrop`, `codePrimPrefix`.

## Owned file (modify this and nothing else)

`Codes2Tape.lean`. ZF-B's two added imports
(`TCSlib.Complexity.TuringMachine.MathlibBridge`, `Mathlib.Tactic.FinCases`)
are sanctioned; flag them. No other import changes are allowed.

## Tasks

**Task 1: re-land target 1 without the copies.**

1. First commit: apply ZF-B's delivered patch,
   `git am -3 audits/evidence/zone-f1-B.patch`, which preserves its
   authorship. It applies cleanly to the issue base.
2. Second commit: **delete each `zfB…` copy whose origin is one of the 46
   names above**, and replace every use with the public name. The mapping
   is `zfBX ↦ codeX` exactly as ZF-B's ledger table lists it; the copies
   were identical after renaming, so the substitution is mechanical. All
   46 deletions are expected.
3. **Keep the rest local.** That is the 20 retargeted two-tape
   adaptations, the 3 format-specific instances `zfBParse_full`,
   `zfBCanonical` and `zfBCanonical_eq`, and the 354-bit regression.
   Watch for false friends: `zfBDecode`, `zfBParse`, `zfBScan`,
   `zfBCanonical`, `zfBReadAction`, `zfBReadTable_append` and similar
   share a `code…` counterpart **name pattern** with *public one-tape*
   functions (`codeDecode`, `codeScan`, `codeCanonical`, …). These are
   **different formats and not interchangeable**. Only the 46 listed
   origins are format-independent.
4. Expected result: about 24 new privates remain; target 1 and its proof
   are otherwise unchanged. The remaining format-specific layer is
   recorded by the maintainer as a 12.2c item, a format-parameterized
   parse layer that would also serve `NDCodes`. **Do not attempt that
   generalization**; it is outside your ownership.

**Task 2: the uniform scheme.** Fill `Turing.exists_uniformMachineCode2`,
the full simulator build, under the inherited contract and ZF-B's
continuation frontier, both below.

**Priority on exhaustion**: Task 1 complete (it is mechanical and
cheap), then Task 2.

## Ground rules (binding)

1. **Statement freeze**; docstring appendices flagged.
2. **Duplication**: after Task 1, **no local copy of a public declaration
   may remain**. The ledger line lists every surviving private with its
   one-tape counterpart, if any, and the share of that counterpart's
   proof it reproduces. New Task-2 helpers are cited, never copied: the
   proved precedents below are public.
3. **Axiom discipline**: both targets at most
   `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. Never touch
   `NDCodes`'s sorried `exists_effectiveNDMachineCode`.
4. **Escalation** on anything unprovable as stated; never restate.

## In-repo proved precedents (cite; never copy)

- The promoted reader layer above, plus `codePrim_machine` (`MathlibBridge`).
- `Encoding.lean`: `CodeTM.serialize`, `MachineCode.decode_encode`, and the
  grammar lemmas `eq_pairEncode_of_pairDecode` and `length_pairEncode`.
- The §13 A-S1 layer (**proved**): `Build/VirtualInput.lean`'s
  `vhostEmitTM`/`vhostSilentTM` and their contracts, which give the input
  discipline for the clocked run.
- `Build/Catalog.lean`'s public rows, including the loop hosts
  `exists_loopTM`/`exists_loopTM_spaceUsed` and the `computesFunInTime_*`
  rows, for the simulator's administrative machinery.

## Inherited audit contract for target 2 (verbatim; binding)

> For the uniform version, check the table's lower-length guard in binary
> **before** expanding the stated number of states. On success the
> table/state administration is polynomial in code length; on failure use
> the fixed fallback. Simulate at most `t` transitions under a binary
> countdown and track output as empty / exactly `[true]` / permanently
> other, since output is append-only. Inspect the result after the
> `t`-th transition before declaring timeout. At `t = 0`, the initial
> configuration is live and its output empty, so the answer is false.
> Fixed scan and lookup costs yield a polynomial jointly in
> `|α| + |x| + t + 1`.

Also binding: the two-work-tape simulation hosts the coded machine's two
tapes on two physical tapes; there is no tape reduction inside the
simulator.

## ZF-B's continuation frontier (from its report; binding)

1. Parse `pairEncode (pairEncode (Nat.bits t) α) x`, keeping the deadline
   in binary. Implement the same canonical count, successor range checks,
   351-per-state guard, and all-true suffix rule as `zfBDecode`. Compare
   the guard **in binary before any per-state iteration**, including for
   malformed enormous counts; a failed decode means the fixed fallback.
2. Host the coded machine's two work tapes on two simulator tapes, with
   the administrative tapes separate. Cite the proved virtual-input and
   catalog machinery for input access, scans, bounded loops and cleanup.
3. Simulate at most the numeric deadline, inspecting the result after the
   last permitted transition. Maintain the append-only output
   classification. Prove that deadline zero rejects.
4. Prove both exact bounded-acceptance branches against
   `(zfBDecode α).toFinTM.ComputesInTime x [true] t`, and derive one
   coefficient/degree bound `simDegree * (α.length + x.length + t + 1)^simDegree`
   for both. The arbitrary-time canonizer theorem **cannot** supply this
   polynomial and must not be used to hide decoding costs.
5. Use the **same concrete effective scheme** as target 1, building its
   canonizer through `codePrim_machine zfBCanonical zfBPrimCanonical`.
   Merely choosing the witness of `exists_effectiveMachineCode2` loses the
   concrete decoder equation.

## Environment and verification

The standard fill setup: the 65-module bootstrap, the Build files,
`CodeParser`, `MathlibBridge` and `Codes2Tape`; **never `lake build`**.
Final checks:

- `Codes2Tape` with zero errors and zero sorry warnings;
- the `TuringMachine` facade with zero errors (`Codes2Tape` is not yet
  facade-wired, so check it directly);
- axiom prints for both targets;
- lint on `TCSlib/Complexity/TuringMachine`, 0 FAIL.

List the tree's remaining admissions as you observe them.

## REPORT.md checklist

- [ ] Task 1: deletions listed (expected 46); surviving privates with
      roles and one-tape counterparts.
- [ ] Task 2: 2/2, or target 1 complete plus a frontier; base hash.
- [ ] Duplication ledger line, as required by ground rule 2.
- [ ] Final sweep tail, 2 axiom prints, and the lint line.
- [ ] Diff touches only `Codes2Tape.lean`.

## Known pitfalls at this pin (hard-won)

- Huge declared state counts: the binary guard check must precede any
  per-state iteration. Expanding unary state counts first is the exact
  EXPCOM-era failure mode.
- `EffectiveMachineCode2` deliberately bounds no decoding time; do not
  strengthen it. Do not weaken `UniformMachineCode2`'s **joint**
  polynomial: never `log t` in the budget, and never drop the rejection
  branch.
- Use the public `eq_pairEncode_of_pairDecode` and `length_pairEncode`,
  not re-derivations.
- The style linter requires a literal "Proof sketch" before **every**
  `sorry`; this matters only for a partial delivery.
