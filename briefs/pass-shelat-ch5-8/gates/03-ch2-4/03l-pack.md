# Gate 03l ([PS10] ch. 2–4, machine infrastructure): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/l/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the machine constructions under the randomized machine model: pair splitting, unary multiplication, the iterate-and-find loop, the state loop, and the string loops. Run 3b proved them, and every frozen machine-layer statement was checked unchanged against the freeze (56/56).
- **This is a "rest" pack.** Its files mostly hold the proofs of headline theorems stated in
  earlier packs, so its trusted surface is their **auxiliary statements**, definitions and
  sketches. A wrong auxiliary statement can make a proof hold for the wrong reason, or hide a
  weaker result behind a headline.
- **Gate type:** an external **statement gate** (`workflow.md` §3), over a layer written in another
  campaign (Frederick Dehmel's, now closed). That layer had only an internal audit (run 3a).
- **The deliverable:** **`gate03l-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs no source pages: these are infrastructure, with [PS10] §2.1 for the machine model.

## Brief for the auditor

Pack 03a's brief applies (its pack is in the bundle), with this emphasis:
- check each **public definition** and each **public theorem statement** against its docstring;
- check each headline's proof sketch against the source's proof, and say where the formal route
  departs from it;
- flag auxiliary statements that are vacuous (unsatisfiable hypotheses), or stronger or weaker
  than their use in the headline needs.

Attempt at least **two adversarial instantiations**. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Complexity/Randomized/Build/{IterateFind, IterateFindHost, PairSplit, StateLoop, StringLoops, UnaryMul}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` |
| Context, not under audit | pack 03a's machine model; `main`'s Turing-machine layer (`Complexity/TuringMachine/`) |
| Design record | `briefs/pass-shelat/DESIGN.md` |
| Inventory | `briefs/pass-shelat/inventory-ch2.md` §5 (the machine-layer requirements consumed by ch. 2) |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/l/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 26 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   17 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 0 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 0 use only the standard axioms, and
   0 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 0 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 6 files.

Pack-specific notes (as drafted): elaboration (a fresh replay of the closure); the axiom prints of
the headlines whose proofs live here; admissions (none in these files); lint.

## Specific questions

1. **Statements.** Is each construction's statement (its function and time bound) what its
   users need? Is any hypothesis unsatisfiable?
2. **The load-bearing loop** (`polyTimeComputable_iterateFind`, as an instance of
   `Turing.FinTM.exists_loopFindTM`). Is the polynomial bound right for polynomially many calls with
   fresh coins?
3. **`main`'s dependencies.** `main`'s `Complexity/TuringMachine/Build/Loop.lean` carries 5
   `sorry`s. Do any of this pack's constructions depend on them? The maintainer's axiom prints
   report it at the pinned head.

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. The pack closes at **0 blockers and 0 majors**.
