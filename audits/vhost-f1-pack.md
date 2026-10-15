# External audit pack — zone/virtual-input layer (§13), tranche A-S1 fill gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4b,
track A). The A-S1 statement gate closed in one round
(`audits/vhost-infra-resolutions.md`); this round audits the **fill**: all
11 audited-true statements of the virtual-input half proved by one batch
(brief `briefs/vhost-f1.md`, report attached verbatim), making
`Build/VirtualInput.lean` and the Z5 statements of `Simulation.lean`
zero-sorry. Epoch gates close on zero blockers and zero majors
(`workflow.md` §4); failure-mode-5 rule in force.

Audited at commit `724108dd` (branch `complexity/arora-barak-ch3-4`). The
fill is the attached single-commit patch (Codex-authored, integrated by
`git am -3` as `4ae4e9b2`; a maintainer doc-only commit then refreshed the
module's stale status header). **Every proof is kernel-checked** — the
maintainer's replay evidence is below — so the audit object is the
**surface**: the one new private declaration, fidelity of the eleven
proofs to the statement-gate audit's binding routes (that audit's
findings are attached — its per-statement arguments were the mandated
proof plans), and the two declared technique notes.

## Brief for the auditor

1. **Blind-restate the single new private declaration**,
   `Turing.vhostSilent_layout`, from its body: it must be exactly the
   layout arithmetic the statement-gate audit verified independently
   (range of `Fin.castAddEmb 1` ↔ value below `1 + m`; complement ↔
   `vhostCap m`; `m = 0` included) — no more, no less. Both silent proofs
   and the silent space proof lean on it; a weaker completeness clause
   (an unaccounted ambient tape) would silently weaken the space ledger.
2. **Check proof fidelity to the binding routes** (the attached
   `vhost-infra-findings.md`, section "The eleven sorried statements,
   literally"): in particular — the step proof adapts, not copies, the
   `bufferedSecondCfg_step` template and cites `bufferTape_inputSymbol` +
   `virtualMove_correct`; the visited statements are proved as
   **equalities** via all-time projection; the silent pair performs **no
   third simulation induction** (two-layer citations only); the space
   proofs keep coefficient one at the same horizon with no output-length
   term on the emit side.
3. **Assess the two declared technique notes**: (i) `virtualMove_correct`
   is consumed at `c.mapState (fun _ => ())` to bridge the existing
   lemma's `S : Type` against the target's `S : Type*` — verify the
   control-only mapping leaves the input position and read definitionally
   unchanged and restricts nothing (a silent universe restriction of the
   frozen statements would be a major); (ii) the buffer/bank sum split is
   implemented with `Fin.addCases` + `Finset.sum_bij`/`sum_erase_add`
   because `Fin.sum_univ_add` is outside the import surface — verify no
   import changed and the split is the true partition.
4. **Freeze**: the maintainer's mechanical check found the patch's
   removals to be exactly the eleven `sorry` bodies, the delivered
   sources byte-identical to the integrated files, and the byte-level
   reconstruction (restore the eleven bodies, drop the one helper)
   recovers the base exactly. Re-establish from the attached patch; also
   verify the maintainer's post-fill status-header refresh (quoted in the
   decision log) is doc-only.
5. **Debt screen (failure mode 5)**: the delivery ledger says "new
   copies: none"; verify the eleven proofs cite rather than restate the
   buffered-host facts (the five prior private rebuilds of this pattern
   remain queued for 12.2c and are untouched).
6. Report anything the fill newly misstates — standard table, standard
   severity scale.

## Repository-side attestations (verify or challenge)

* Freeze (maintainer, mechanical): patch removals are exactly the eleven
  `sorry` lines; one declaration added (private); both delivered full
  sources byte-identical to the integrated files; diff touches only the
  two owned files; the bundle verifies against the recorded base
  `44d25413`.
* Fresh replay (`audits/logs/vhost-f1-integration-sweep.log`): the five
  prescribed modules (`Simulation`, `Build/Embed`, `Build/VirtualInput`,
  `Build/Catalog`, the `TuringMachine` facade) all exit 0 — **0 errors,
  0 sorry warnings**, fresh `.olean`s. (The tree's remaining sorries are
  the A-S2 statement surface, out of scope and in its own gate.)
* Independent axiom prints (`audits/logs/vhost-f1-axioms.log`,
  maintainer-generated): all **11** within
  `[propext, Classical.choice, Quot.sound]` — the two Z5 transfers at the
  proper subset `[propext, Quot.sound]` — and `sorryAx` nowhere.
* Style lint: 0 FAIL; `Simulation.lean` at 1,014 lines under its recorded
  justification; `VirtualInput.lean` 506 lines.
* Delivery integrity: `SHA256SUMS` all OK; duplication ledger "new
  copies: none"; the delivery notes a runtime executable-path shim was
  needed in its environment but ships no shim source and the patch
  references none.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/vhost-f1-findings.md`; the gate closes on zero blockers and
majors, which completes tranche A-S1 end to end (statements, gate, fill,
fill gate) and leaves §13 waiting only on the A-S2 loop.
