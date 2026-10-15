# External audit pack — zone/virtual-input layer (§13), statement gate, tranche A-S1

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4b,
track A; design `machine-library-design.md` §13/§13a). The §13 statement
phase runs in two tranches; this round audits **A-S1, the virtual-input
half**: Z5 (the machine-agreement transfer, `Simulation.lean`, additive),
Z1 (`Build/VirtualInput.lean`, new), and the Z1 rider (four selected-tape
exports in `Build/Embed.lean`, skeleton-time proofs). The zone half
(Z2/Z3/Z4) follows as tranche A-S2 with its own gate. The gate closes on
zero blockers and zero majors (`workflow.md` §3), with the failure-mode-5
rule in force: a debt major closes only by explicit human acknowledgment.

Audited at commit `28a49d69` (branch `complexity/arora-barak-ch3-4`).
**The audit object is the statement surface**: 7 new definitions, 11
`sorry`d contracts (9 in `VirtualInput.lean`, 2 in `Simulation.lean`), and
4 skeleton-time-proved lemmas. The proofs that exist are kernel-checked;
hunt the five failure modes of `audits/TEMPLATE.md` (infidelity,
trivialization, unprovability, missing hypotheses, debt).

## Brief for the auditor

1. **Blind-restate every definition** from its body before reading its
   docstring, and report daylight: `MultiTapeTM.AgreeOn`; `vhostBuffer`/
   `vhostBank`/`vhostCap` (the `1 + m` and `(1 + m) + 1` layouts);
   `vhostCfg` (in particular the buffer-head convention — source input
   position **minus one** — and that a halted source maps to a halted
   host); `vhostEmitTM` (the clamped `virtualMove` discipline, the tag in
   control, the frozen native head, `q₀ = (M.q₀, true)`);
   `vhostSilentTM`/`vhostSilentCfg` (**the layer composing with itself**:
   `embedSilentTM (Fin.castAddEmb 1) (vhostCap m)` over `vhostEmitTM`).
   For the silent pair, verify the composition arithmetic yourself: the
   range of `Fin.castAddEmb 1` on `Fin (1+m)` misses **exactly** the
   capture tape, so the transport's ambient frame parameters
   (`fun _ _ => none`, `fun _ => 0`) are inert — confirm or exhibit a tape
   they touch.
2. **Argue each of the 11 sorried statements true as literally stated**,
   or exhibit the problem. The binding inherited contracts are the A2/F2
   audit clauses (attached `batchF2A2-REPORT.md` and the F2 findings'
   forwarding ledger): both boundary clamps with **no nonempty-`y`
   premise**, halt absorption, the source's halting emission executed
   before the control dies, coefficient-one space on the hosted bank. The
   named fill template is the proved
   `Turing.FinTM.bufferedSecondCfg_step`/`_run` — compare statement shapes
   and flag any weakening (note the visited-set statements claim
   **equality**, not containment).
3. **Adversarial instantiations** (at least eight): `y = []` (boundaries
   adjacent — both clamps, tag at `p.val = 1` forced `true`); `m = 0` (a
   bank-free source: the host is one buffer tape); `t = 0`; an initially
   halted `c`; a source action attempting the outward move at each
   boundary under each tag; the emitting halting step (does
   `vhostEmitTM_emitting_halt`'s output parse `(pre ++ c.output) ++ [bit]`
   match the step identity?); native `x = []` (`p : Fin 2`); nonempty
   `pre`/`capPre`. For Z5: `Q = ∅`, `Q = Set.univ`, a run that halts
   before `t`, machines agreeing nowhere outside `Q`.
4. **Z5 strength check against its named customers** (design §13 Z5;
   evidence attached in `retrofit-inventory/loop.md`): the forwarding loop
   host agrees with the capturing host on every non-body state — is
   `AgreeOn` + `runFrom_eq_of_agreeOn`'s visit hypothesis (`∀ u < t`,
   live states in `Q`) sufficient to collapse the fourteen re-proved phase
   lemmas, and sufficient for the guarded `clSlot_run`-style sites, or do
   those need a per-configuration (not per-state) agreement form? If the
   statement is too weak for the named customers, that is a major.
5. **The four rider lemmas** (`embedSilentCfg_selected_tape`/`_pos`,
   `embedEmitCfg_selected_tape`/`_pos`): skeleton-time proofs, flagged —
   blind-restate them and confirm they are the selected-tape projections
   the three retrofit inventories requested (the D-R1 blocker), and that
   their statements expose nothing beyond the transports' fields.
6. **Space-ledger shapes**: `vhostEmitTM_spaceUsed_le`'s constant
   (`y.length + 2`) and the silent bound's capture term
   (`(capPre ++ (M.runFrom c t).output).length + 1`) — right constants,
   right horizon, coefficient one on `M.spaceUsed`? The intended consumer
   of the silent ledger is the `NP^EXPCOM ⊆ EXP` query simulation; flag a
   shape that consumer cannot use.
7. **Debt screen (failure mode 5)**: this tranche must add **no new
   copies** of existing proved material. The five prior private
   re-derivations (`bufferedCompTM` phase two aside, which is public and
   stays) remain in place pending the recorded 12.2c dedup — verify the
   new file *defines* rather than copies (the transformer is new public
   surface; its contracts cite, not restate, `virtualMove_correct`), and
   verify the maintainer's ledger line below.
8. Report anything the statements misstate, in the standard table and
   severity scale; propose any missing machine-checkable sanity theorem
   (candidates you should weigh: an `initCfg`-free statement that the
   `q₀` tag claim in `vhostEmitTM`'s docstring is actually consumed
   nowhere; a `vhostCfg` injectivity/ext lemma; the emit flavor's
   `visitedByTapeHead` for the *native* input — note the native head is
   frozen by the run identity).

## Known deviations and declared anomalies (verify they are benign)

* The four rider lemmas are **proved at statement time** (rfl-grade at the
  private `embedSlot_selected`), keeping the closed `Embed.lean`
  zero-sorry; precedent: the P3.1/P4.1 skeleton-time proofs.
* `vhostSilentTM` is a **definition by composition**, not a bespoke
  machine; its two contracts are deliberately stated on the composite and
  sketched as two-layer citations. If you judge the composite statements
  underdetermined (e.g. the inert-frame analysis fails), that is a major.
* `Simulation.lean` crosses the size policy line at 1,005 lines; the
  justification (decision 13.5, additive growth, D7 split window) is
  recorded in the plan's decision log.
* The `q₀ := (M.q₀, true)` tag is asserted valid at the canonical start
  position in a docstring; no contract consumes `q₀`. Flag if any
  statement silently depends on it.

## Repository-side attestations (verify or challenge)

* Elaboration: `Simulation`, `Build/Embed`, `Build/VirtualInput` all check
  with exit 0, zero `error:` lines, fresh `.olean`s; exactly **11**
  `declaration uses 'sorry'` warnings (9 + 2); `Embed.lean` remains
  zero-sorry.
* Style lint: 0 FAIL over both directories; the one new WARN
  (`Simulation.lean` size) is justified as above; every `sorry` carries a
  literal **Proof sketch**.
* **Duplication ledger (failure mode 5): new copies — none.** The file
  defines new public surface; the five in-repo precedents are untouched
  and queued for 12.2c.
* Base: the statements were landed in one maintainer commit at
  `28a49d69`; no other file changed.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md` (including failure mode 5);
findings verbatim into `audits/vhost-infra-findings.md`; the gate closes
on zero blockers and majors, after which the A-S1 fill epoch dispatches
and tranche A-S2 (the zone half) is drafted.
