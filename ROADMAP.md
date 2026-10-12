# Roadmap

A one-page orientation for the Arora–Barak campaign and the library foundations under it. It is
intentionally brief. Every line points to the document that holds the detail, and that document
is authoritative. Update this file when a phase starts or ends, not for progress within a phase.

*Last updated 2026-10-12.*

## Where things stand

- **Chapters 3–4.** The inventory is in `AroraBarakChapters3-4Plan.md` §4e. Current status is in
  the latest rows of its decision log. Snapshot for 2026-10-12: of 94 statements, 60 are proved,
  7 are proved modulo open library rows, and 27 are open. Eight fill batches are in flight (`briefs/`).
- **Machine library.** `TCSlib/Complexity/TuringMachine/Build/`, designed in
  `machine-library-design.md` §12–§13.
- **Programming layer.** `TCSlib/Programs/`, vendored from [AFM26]: design §15–§15b.

## Phases

1. **Land the current wave.** Integrate the in-flight deliveries and close their gates. The
   briefs are in `briefs/`; the open gates are `audits/12.2c-t2a-pack.md` and
   `audits/programs-vendor-pack.md`.
2. **Foundations**, in parallel:
   - the contract structure (MIG-0);
   - named witnesses and the `f2_` deletion (MIG-1);
   - the language extensions: input read in place, `emit`, and the coin stream (design §15a);
   - designs for B4 hardness, B6 and C1 (design §14).
3. **Build on them:**
   - stage 2, the RAM-to-`FinTM` compiler (design §15a);
   - B4 hardness and B6, through the hosts H2, H3, H5 and H6 (design §14);
   - rebasing Build on contracts (MIG-11 to MIG-17).
4. **Chapter work on the language side:**
   - machine-configuration routines, then Savitch and PSPACE = NPSPACE (design §16, decision 3);
   - S1b re-derived as a program (MIG-19);
   - C1, the NTIME hierarchy;
   - C2, PATH and Immerman–Szelepcsényi.
5. **Closure.** The campaign closure gate and the blueprint (`workflow.md` §5), §13d G2–G4 (design
   §13d), and the remaining RS items.

**At any time:**
- the intro-algorithms curriculum (design §15, layer L4);
- the asymptotics port (MIG-18);
- RS restyling items.

12.2c is folded into the migration (plan §4e, head of the 12.2c tasklist).

## Critical paths

- **Chapter 3:** W2-S, B5a and B5b, then Baker–Gill–Solovay; then C1.
- **Chapter 4:** MIG-0, then stage 2, the extensions, the configuration routines, Savitch, and
  PSPACE = NPSPACE.

## Decisions ahead

The open questions are in `backlog.md` §1 and §4, and in the open-decision lists of design §15
and §16. The next ones are:
- MIG-0's statements;
- the semantics of the extensions;
- B4a's explicit restatement (Finding A);
- B6's re-route;
- C2's route;
- the scope of §13d G2–G4.

## Where to find what

| For | See |
|---|---|
| How campaigns run (phases, gates, briefs, delivery) | `workflow.md` |
| Standards for landed code | `policy.md` |
| Library design: routines, hosts, the programming layer, the migration | `machine-library-design.md` §12–§16 |
| Chapters 3–4: plan, inventory, decision log | `AroraBarakChapters3-4Plan.md` |
| Open items, the MIG/RS backlog, human-review questions | `backlog.md` |
| Briefs for fill agents | `briefs/` |
| Audit packs, findings, evidence | `audits/` |
| Earlier chapters | `AroraBarakChapter1Plan.md`, `AroraBarakChapter2Plan.md`, `AroraBarakChapter7Plan.md` |
