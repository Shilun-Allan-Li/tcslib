# Dispatch · gsw-6a-statements, issued-6a-r1 (Claude, lead plus up to 2 sub-agents)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/7ad533f9a9166f5661f13ff7dfb6904e8a0a67c3/outbox/fills/gsw-6a-statements)
is staged on the exchange at `7ad533f9a9166f5661f13ff7dfb6904e8a0a67c3` (local branch `stage/gsw-6a-exchange`,
parent `78d89c5cda437ae1bea629328eb3116e2f36d026`; **not yet pushed**, so the link resolves only after the push).
Brief SHA-256 `215978b24fb73d448922da88e9f80bd9b914372340a670de89eaa57fa23a3adb`. The worker is Claude under
Seyoon's ruling of 2026-11-16 (the 6a statements go to an external Claude session; lead plus up to 2 sub-agents).
Seyoon dispatches.

**Base.** `f6f295a6502b72bbf498bb8c64b63f847e910866`, the records tip at issue; its Lean is the merged #327/#324
state.

**Records pin.** `<RECORDS-PIN>`: the records commit that carries plan section r3 and this folder. The maintainer
writes its full hash here, and in the prompt below, after committing.

**Before dispatch** (maintainer):
1. Commit `briefs/lattice-gsw/phase6/plan-section.md` (r3, SHA-256
   `06824b3db875e7388771b6f7a5e78d62bf7d77fa35571fc3a9deeebc329214fd`, equal to the pack's
   `inputs/plan-section-r3.md`) and `briefs/lattice-gsw/phase6/issued-6a-r1/`; put that commit's full hash for
   `<RECORDS-PIN>` in the **Records pin** line and in the prompt.
2. Push the exchange commit. If it is replayed onto a newer exchange tip (the tip was
   `4a64f6ed23d7b2a80e307f9b280fc01c959f33b3` at staging, an Arora–Barak gate-149 commit; the replay merges
   cleanly), put the pushed hash in the pack link, the staging line and the prompt.

## Prompt for Claude (lead plus up to 2 sub-agents)

```text
You are the lead Claude worker for the GSW phase-6a statement job
gsw-6a-statements (lattice campaign) in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned
Mathlib). You may use up to 2 sub-agents.

1. Read exchange/pass-shelat-ch5-8 at
   7ad533f9a9166f5661f13ff7dfb6904e8a0a67c3. Read README.md and
   outbox/fills/gsw-6a-statements/README.md, brief.md,
   fill-environment-addendum.md and inputs/ (plan section r3, the
   rulings, the Bar89 ingest). Verify the pack with SHA256SUMS and
   inputs/SHA256SUMS (shasum -a 256 -c). You are the lead the brief
   describes. The records of this issue are at commit <RECORDS-PIN> of
   cryptography/pass-shelat-ch2-4 (briefs/lattice-gsw/phase6/
   plan-section.md and issued-6a-r1/, equal to the pack's copies).
2. In a separate clone, fetch cryptography/pass-shelat-ch2-4 and start at
   the issue base f6f295a6502b72bbf498bb8c64b63f847e910866. Keep every
   branch local. First write owner PR O1 on owner/o1-balanced, proved:
   TreeNCAC.combine promoted as TreeCircuit.balanced in the new
   FormulaArith/Combinators.lean with the facade FormulaArith.lean,
   TreeNCAC re-pointed, the moved proofs byte-identical except the three
   Rule 10 repairs the brief names. Then, on stmt/gsw-6a from O1's head,
   write the 6a statement phase exactly as the brief and plan section r3
   specify: BranchingPrograms/{Defs,Eval,Barrington,BarringtonConverse,
   NC1} and its facade, NANDForm, NANDLayering, FormulaArith/{Combinators,
   CarrySave,Compare,ModSum}, the registrations in ComputationalModels.lean,
   CircuitComplexity.lean and TCSlib.lean, and the registry rows H18-H20
   with the gadget subsection in machine-library-design.md. Every
   definition gets its body and its readers proved; every target is
   sorry'd with its formula docstring, source tag and proof sketch;
   everything compiles. Nothing of 6b: no Cryptography/ file, no O2, no
   [Gen09]. Follow the binding rulings the brief lists, policy.md and the
   standing rules: frozen files change only by a scope request to Seyoon;
   readers only (Rule 10); line width at most 100; no @[simp]; cite only
   ingested sources and never fabricate an excerpt. Use only narrowed
   Mathlib roots, never lake build and never an unfiltered lake exe cache
   get, and check one module at a time with scripts/lean_check_tree.sh.
   Run Python as python3 -I.
3. Run the brief's checks: the builds of the closure and of the root;
   the statement list (decls2) with the r3 row map; sorry and admission
   counts against base-sorries.txt; axioms with a dependency trace; Rule
   10 seals A and B, strict and coe, with paired controls on every new
   owner, and the reader census; the probes P1-P10 (yield order, the
   commutator c[0,2,1,4,3], the computable conjugator, Lemma 2, Theorem 1,
   the host, Theorem 2, the NAND gadget, the layering, the formula
   arithmetic); the frozen-file check; lint; file sizes; the name-clash
   scan; and the reuse and overlap disclosures against r3 section H2. If a
   probe shows an r3 statement false, do not weaken it silently: report
   it as a question for Seyoon.
4. Sub-agents (at most 2): each owns a disjoint set of files, has its own
   git worktree and its own TCSlib olean tree, with .lake/packages linked
   to yours; only you run lake and fetch the cache. One Lean process at a
   time on the host, for all agents together, through one lock. Only you
   commit on owner/o1-balanced and stmt/gsw-6a, run the final checks and
   deliver. Sub-agent logs go under evidence/subagents/<name>/; REPORT.md
   records who wrote what.
5. Deliver checkpoint 1 (O1 complete, with Defs, Eval and NANDForm
   compiled) and the final payload only under
   inbox/fills/gsw-6a-statements/ on exchange/pass-shelat-ch5-8:
   REPORT.md; patches/o1/ and patches/stmt/, each with COMMITS.tsv and
   its signing column (commit both series with commit.gpgsign=false);
   src/ and src-o1/; evidence/ with its manifest; and the top-level
   SHA256SUMS (paths equal to the delivered files). Pull with rebase
   before pushing. Never force-push, never edit another path and never
   push a campaign branch. The maintainer will review the result for O1
   and a stacked statement PR that Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material.
```

After the two steps above:

**Ready to dispatch**
