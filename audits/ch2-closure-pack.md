# Chapter-2 campaign closure pack

The consolidated closure record required by `workflow.md` §5, assembled
at E5 closure. It is a record, not a new audit round: every constituent
gate below is CLOSED with its own findings/resolutions on file, and the
chapter's final state is attested by the evidence listed at the end.

## The campaign, end to end

**Result.** All 59 original Chapter-2 admissions ([AB09] ch. 2) are
proved on the campaign's own machine model: the polynomial-time
calculus; the NDTM run calculus and `NTIME`; complementation and the
easy inclusions; the CNF formula mathematics; `NP ⊆ EXP`; the HALT
pair; Theorem 2.6 both directions; `TMSAT` NP-completeness with the
quantitative universal-machine bridge; the exponential padding cluster
through `EXP ⊆ NEXP` and `NEXP = ⋃ NTIME(2^(n^c))`; `SAT` and `3SAT`
membership; Lemma 2.14 (`SAT ≤ₚ 3SAT`) as a streaming emit-loop
machine; the five snapshot-locality lemmas on the oblivious model;
**Cook–Levin (Theorems 2.10.1–2.10.2)** — `SAT_NPHard`,
`SAT_NPComplete`, `SAT3_NPHard`, `SAT3_NPComplete` — via the certified
tableau route (packed-record producer, ordered emission under one
common polynomial budget, physical output identity, then pure
equisatisfiability); and `TAUTOLOGY` coNP-completeness (Example 2.21,
DNF fragment) via the dual transducer. Axioms everywhere: at most
`propext`, `Classical.choice`, `Quot.sound`.

## The closed gates (chronological)

| Gate | Scope | Record | Position |
|---|---|---|---|
| Phase 1–4 statement gates | the 59-statement trusted surface, in four phases | `audits/ch2-phase{1,2,3,4}-*` (+ reaudits/round 3) | CLOSED |
| Epoch-1 fill gate | the working calculus (10 targets) | `audits/ch2-epoch1-*` | CLOSED |
| Epoch-2 fill gate | Thm 2.6, Ex 2.1, HALT, TMSAT (10 targets, 386 privates) | `audits/ch2-epoch2-*` | CLOSED, PASS round 1 |
| Emitter statement gate | the §11 emitter-increment contracts | `audits/emitter-infra-*` (3 rounds) | CLOSED |
| Emitter fill gate | the seven emitter contracts | `audits/emitter-fill-*` | CLOSED, PASS round 1 |
| Epoch-3/4 fill gate | the 21 remaining targets incl. Cook–Levin and TAUTOLOGY (1,206 privates); ride-alongs: both carrier/infra merges, the duplicate-dispatch governance | `audits/ch2-epoch34-*` (3 rounds) | CLOSED, PASS round 3 |

Chapter-6 interface: the colleagues' circuit surface passed its own
protocol (`audits/ch6-circuits-*`, 3 rounds, CLOSED); campaign
statements cite it under the recorded divergences.

## E5 closure actions (this record's commit span)

1. **Dedup of superseded fill strata** — per the gate's approved
   disposition: kernel-derived live/dead inventory preserved before
   deletion (`audits/evidence/ch2-epoch34/e5-dedup-inventory.md`),
   **153 dead privates deleted, 20 kernel-dead roots kept on textual
   grounds**, Snapshot untouched; deletion-only, whole blocks, no
   deletion by prefix or label; the adopted named cases verified.
2. **Drift attestation** — `audits/evidence/ch2-epoch34/`
   `e5-drift-attestation.md`: against the gate-audited baseline
   (`154ecb18`, the round-2/3 manifest), every changed module's
   retained declaration sequence is an **ordered subsequence** of the
   baseline, and public drift is **none**; unchanged modules are
   byte-identical.
3. **Zero-sorry closure sweep** — fresh 65/65, zero `error:` lines,
   zero `sorry` warnings (`audits/logs/ch2-e5-closure-sweep.log`).
4. **Closure traversal** — the committed round-3 program re-run on the
   post-dedup tree (`audits/logs/ch2-e5-closure-axioms.log`): the 21
   targets empty-rooted at the standard triple; the 87-name kernel
   surface unchanged by the dedup; the whole-closure axiom bound holds.
5. **Blueprint increment** — deferred to the main merge (user decision),
   completed 2026-10-07 on the merged tree: dependency graph rebuilt from
   the first post-ban `lake build` (425 modules / 9,707 declarations);
   **all 33 campaign-surface modules documented, 2,259 entries**; a
   uniform strict-rubric pass flagged 178 entries (all from five writers
   that skipped the per-entry check), repaired with structural lines
   verified byte-identical, re-run **0 quality / 0 hygiene flags**;
   `blueprint_assemble.py` wired 28 new chapters; `blueprint_validate.py`
   **0 dangling `\uses`, zero campaign-namespace orphans** (two stale ch1
   entries for lemmas deduplicated by colleague merge #2 removed, their
   edges retargeted to the shared `Turing.length_bits_le_self`). The 189
   colleague-tree modules (3,574 declarations) are left to their owners.

## Final state

- Ledger **59/59**; the 65-module campaign surface admission-free.
- Owned-file sizes after dedup: Hardness 8,904; SAT 4,635;
  Nondeterminism 4,416; EXP 3,237; Tautology 1,728; Snapshot 368 —
  all five exceptions reduced, all still recorded pending the approved
  routine-layer retrofit.
- Standing post-closure queue (recorded decisions): the §12
  machine-routine layer design → statement gate → fills → audit; the
  ch1+ch2 retrofit (Cook–Levin included); D7 splits fold into the
  retrofit; the ch3 planning alignment with the colleague's
  TimeHierarchy tree.
