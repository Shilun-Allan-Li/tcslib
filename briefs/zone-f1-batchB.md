# §13 fill campaign — Tranche A-S2, Batch ZF-B: the two-tape code schemes (`Codes2Tape.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`** — this exact branch,
  NOT `main`.
- Create your working branch off it (suggested name `fill/zone-f1-B`),
  record the base commit hash in `REPORT.md` (the brief was issued at
  `8f13d74ecba8e73a3642d605f462774092d7ef8a`), and never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `zone-f1-B.zip` with the standard contents (report, full source,
  format-patch series, bundle, sweep log, axiom log, `SHA256SUMS`).

## Context

You are filling the **2 audited-true statements** of
`TCSlib/Complexity/TuringMachine/Codes2Tape.lean`:
`exists_effectiveMachineCode2` and `exists_uniformMachineCode2`. The
statement gate closed in three rounds
(`audits/zone-infra-{,r2-,r3-}findings.md`, summary
`audits/zone-infra-resolutions.md` — read them; Z3 drew **no findings in
any round**, and the round-1 report verified the record format and
grammar numbers quoted below). This is the batch with **continuation
budget risk**: two targets, but each is a full parser/canonizer or
simulator build. Batches ZF-A (`Build/Zone.lean`) and ZF-C (Robustness)
run concurrently — you never touch their files.

## Owned file (modify this and nothing else)

`Codes2Tape.lean` (199 lines, 2 sorries). Fill order: target 1 feeds
target 2 (the uniform scheme extends the effective one).

## Ground rules (binding)

1. **File ownership**: only `Codes2Tape.lean`; `private` helpers only;
   shared wishes via "Requested shared lemmas" with a `private` local
   copy — and under `policy.md` **Duplication**, every local copy is
   disclosed in the ledger line and needs the maintainer's eye before
   integration; prefer citing the public precedents below outright.
2. **Statement freeze**; docstring appendices flagged.
3. **Escalation** on anything unprovable as stated.
4. **Continuation budget**: deliver target 1 complete rather than both
   partial; a partial zip follows the standard rule.
5. **Axiom discipline**: both targets at most
   `[propext, Classical.choice, Quot.sound]`, no `sorryAx` — in
   particular your proofs must not touch `NDCodes`'s sorried
   `exists_effectiveNDMachineCode` (its import supplies only
   `actionBits₂`/`workPair`, which are definitions).

## In-repo proved precedents (cite; never copy)

- `TCSlib/Complexity/TuringMachine/CodeParser.lean` — the received parser
  architecture for the one-tape `actionBits` table (proved, chapter 1).
- `TCSlib/Complexity/TuringMachine/MathlibBridge.lean` —
  `Turing.exists_effectiveMachineCode`'s arbitrary-time canonizer route
  (proved; its polynomial variant is explicitly superseded).
- `TCSlib/Complexity/TuringMachine/Encoding.lean` — `CodeTM.serialize`,
  `MachineCode.decode_encode`, the grammar lemmas
  (`eq_pairEncode_of_pairDecode`, `length_pairEncode`).
- The §13 A-S1 layer (**proved**): `Build/VirtualInput.lean`'s
  `vhostEmitTM`/`vhostSilentTM` and their contracts — the input
  discipline for the uniform simulator's clocked run.
- `Build/Catalog.lean`'s public rows (incl. `exists_loopTM_spaceUsed`'s
  time clause and the `computesFunInTime_*` rows) for the simulator's
  administrative machinery.

## Inherited audit contract (verbatim; binding)

From the round-1 findings (A-S2-8, verified again in round 3):

> The shared record has minimum length 13, hence the table guard is
> `351*(numStates+1)`, versus 702 for ND. [...] Each record has length 13
> for halt, or `14 + s.val` for a successor. The enumeration contains
> `(numStates+1)·3·3·3 = 27(numStates+1)` records. [...] The exact
> serializer-length identity is
> `|M.serialize| = 2|Nat.bits(M.numStates)| + M.tm.q₀.val + 3 +
> 351(M.numStates+1) + Σ_{records with successor s}(s.val + 1)`.
> At `numStates = 0`, the minimum complete deterministic serialization is
> `2 + 1 + 27·13 = 354` bits. [...] Only the **table term**, not the
> header-inclusive length, halves [against ND].

> For existence, parse and range-check the concrete grammar, accept only
> all-true suffix padding, and fall back to a fixed one-state halting
> machine on failure. A table has a fixed number of self-delimiting
> successor records; appended true bits cannot change already-parsed
> records. Finite tables over finite domains reconstruct the exact
> machine, including initial state. A terminating canonizer reserializes
> the result; a maximum over the finitely many strings of each length
> supplies its arbitrary time bound.

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

Also binding (the statements' own sketches): `encode := Code2TM.serialize`
itself; `decode_encode_pad` is property 2; the two-work-tape simulation
hosts the coded machine's two tapes on two physical tapes — no tape
reduction inside the simulator.

## Optional permanent lemmas (audit-adopted; flagged)

The exact serializer-length identity; the `351·(numStates+1)` parser-guard
lemma; the `numStates = 0` (354-bit) regression; `actionBits₂`
exact/minimum length lemmas.

## Environment and verification

As the standard fill setup (65-module bootstrap + the Build files +
`Codes2Tape`; never `lake build`). Final: `Codes2Tape` with zero errors
and zero sorry warnings, then the `TuringMachine` facade (zero errors; the
tree's remaining sorries are ZF-A/ZF-C's concurrent surfaces and the
baseline admissions — list them in `REPORT.md` as observed). Axiom prints
for both targets. Lint on `TCSlib/Complexity/TuringMachine` — 0 FAIL.

## REPORT.md checklist

- [ ] 2/2 (or target 1 complete + frontier); base hash; every new
      `private` listed with roles; requested shared lemmas or "none".
- [ ] Duplication ledger line; any local copy disclosed individually.
- [ ] Final sweep tail + 2 axiom prints + lint line.
- [ ] Diff touches only `Codes2Tape.lean`.

## Known pitfalls at this pin (hard-won)

- The style linter requires a literal "Proof sketch" before **every**
  sorry — relevant only if you deliver a partial with sorried privates.
- `pairEncode`/`pairDecode` grammar work: use the public
  `eq_pairEncode_of_pairDecode`/`length_pairEncode`, not re-derivations.
- The P3.2 lesson is binding context: `EffectiveMachineCode2` deliberately
  bounds no decoding time; do not strengthen it, and do not weaken
  `UniformMachineCode2`'s **joint** polynomial (never `log t` in the
  budget; never drop the rejection branch).
- Huge declared state counts: the binary guard check must precede any
  per-state iteration — expanding unary state counts first is the exact
  round-1 EXPCOM-era failure mode.
- `Function.update_of_ne`; `dsimp only` after `cases` on control; `omega`
  needs beta-reduced goals; avoid bare `simp` on folded forms.
