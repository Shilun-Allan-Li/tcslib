# §13 fill campaign — Tranche A-S2, Batch ZF-B3 (continuation): the uniform two-tape scheme (`Codes2Tape.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch,
  NOT `main`.
- Create your working branch off it (suggested name `fill/zone-f1-B3`).
  Record the base commit hash in `REPORT.md`; the brief was issued at
  `2623e2eb0c37436f2db611a75c1f90d9dc54203e`. Never rebase.
- **Delivery is by zip, not PR or push**: `zone-f1-B3.zip` with the
  standard contents (report, full source, format-patch series, bundle,
  sweep log, axiom log, `SHA256SUMS`).

## What this is

This is the second continuation of batch ZF-B. Read `briefs/zone-f1-batchB.md`
and `briefs/zone-f1-batchB2.md` in full; everything there binds unless
amended here. ZF-B2's Task 1 is integrated: `exists_effectiveMachineCode2`
is proved, the 46 copies are gone, and 24 two-tape privates remain. Its
report is `audits/zone-agent-reports/f1-B2-REPORT.md`, and its Task-2 notes
are `audits/zone-agent-reports/f1-B2-CONTINUATION.md`; read both. **Your one
target is `Turing.exists_uniformMachineCode2`.**

ZF-B2 stopped on a defect in the B2 brief, which forbade new imports while
requiring citations of unimported modules. **That is resolved (user
decision, 2026-10-10).** You may add exactly these two imports to
`Codes2Tape.lean`, and must flag them:

```lean
import TCSlib.Complexity.TuringMachine.Build.VirtualInput
import TCSlib.Complexity.TuringMachine.Build.Catalog
```

Nothing in the repository imports `Codes2Tape.lean`, so these cannot create
a cycle. No other import changes are allowed.

## Owned file (modify this and nothing else)

`Codes2Tape.lean`: the target's proof plus new `private` helpers. The
effective scheme, its proof, and the 24 existing privates are **frozen and
byte-identical**; reuse them, in particular the concrete `zfBDecode` and
the canonizer built from `codePrim_machine zfBCanonical zfBPrimCanonical`.

## Ground rules (binding)

1. **Statement freeze**; docstring appendices are allowed if flagged.
2. **Duplication**: no copy of any public or private declaration from
   another file. The 23 two-tape parse-layer instances are acknowledged
   debt (12.2c tasklist item 8); **do not add to them**. A Task-2 helper
   that re-proves a one-tape parser fact is a copy. List every new private
   with its role in the ledger line.
3. **The canonical-only caution** (ZF-A2's finding,
   `audits/zone-agent-reports/f1-A2-REPORT.md`, "Why canonical transfer is
   insufficient"). The §12 catalog rows (`transferTM_run`, `copyTM_run`,
   `clearTM_run`, …) start from `Cfg.ofWords`: heads at zero and globally
   buffered tapes. Use them only where your configuration really is
   canonical, such as setup on fresh administrative tapes. If you need one
   on a displaced or framed configuration, **do not re-derive it**: request
   one public shared lemma under "Requested shared lemmas". A §12 framed
   contract batch is being commissioned in parallel.
4. **Axiom discipline**: at most `[propext, Classical.choice, Quot.sound]`,
   no `sorryAx`. Never touch `NDCodes`'s sorried
   `exists_effectiveNDMachineCode`.
5. **Escalation** on anything unprovable as stated; never restate.

## The binding route

The inherited audit contract for the uniform version and ZF-B's
continuation frontier are quoted verbatim in `briefs/zone-f1-batchB2.md`;
both stay binding. ZF-B2's `CONTINUATION.md` restates them with two useful
specifics:

- Cite the public `Turing.FinTM.not_computesInTime_zero`
  (`Finite.lean`) for the source-side zero-time fact; the simulator must
  still implement its `false` answer.
- `Turing.vhostEmitTM`/`Turing.vhostSilentTM` are in namespace `Turing`,
  not `Turing.FinTM`.

In short:

- Parse `pairEncode (pairEncode (Nat.bits t) α) x` with the deadline and
  the claimed state count kept in binary, and check the guard
  `351 * (n + 1) ≤ rest.length` **before** any per-state expansion. On
  failure, use the fixed fallback.
- Host the two coded work tapes on two physical tapes, with administration
  and the virtual input separate; there is no tape reduction.
- Simulate at most `t` transitions under a binary countdown, keeping the
  append-only output status. Inspect after the last permitted transition;
  deadline zero rejects.
- Prove both acceptance branches with **one joint polynomial** in
  `|α| + |x| + t + 1`.

## Environment and verification

The standard fill setup; **never `lake build`**. Final checks:

- `Codes2Tape` with **zero errors and zero sorry warnings**;
- the `TuringMachine` facade with zero errors (`Codes2Tape` is not
  facade-wired, so check it directly);
- axiom prints for both targets;
- lint on `TCSlib/Complexity/TuringMachine`, 0 FAIL.

## REPORT.md checklist

- [ ] 1/1, or a frontier; base hash; the two imports flagged.
- [ ] Every new `private` with its role; requested shared lemmas, or
      "none".
- [ ] Duplication ledger line, per ground rule 2.
- [ ] Final sweep tail, 2 axiom prints, and the lint line.
- [ ] Diff touches only `Codes2Tape.lean`.

## Known pitfalls at this pin (hard-won)

- **Huge declared state counts.** The binary guard check must precede any
  per-state iteration.
- Never weaken `UniformMachineCode2`'s **joint** polynomial: no `log t` in
  the budget, and never drop the rejection branch. The arbitrary-time
  canonizer theorem cannot supply the simulator's polynomial.
- Through-halt contracts need `(hc : c.state ≠ none)`.
- `Function.update_of_ne`; `dsimp only` after `cases` on control.
- The style linter requires a literal "Proof sketch" before **every**
  `sorry`; this matters only for a partial delivery.
