# Gate 03i ([PS10] ch. 2–4, Goldreich–Levin and hard-core results): external statement audit pack

**Status: draft.** The pinned head, the attestations and the bundle are filled in once the dedup PR has landed
(`PLAN.md`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`<HEAD, 40 hex, from git rev-parse>`. This pack covers the proof of the Goldreich–Levin theorem (Thm 87.3) and its collection form, the hard-core lemmas behind the PRG constructions (Thm 79.4, Lem 80.5), the hard-core bit of one-way permutation collections, and the ensemble lemmas (the hybrid and prediction lemmas, Lems 71.5, 71.6, 73.8).
- **This is a "rest" pack.** Its files mostly hold the proofs of headline theorems stated in
  earlier packs, so its trusted surface is their **auxiliary statements**, definitions and
  sketches. A wrong auxiliary statement can make a proof hold for the wrong reason, or hide a
  weaker result behind a headline.
- **Gate type:** an external **statement gate** (`workflow.md` §3), over a layer written in another
  campaign (Frederick Dehmel's, now closed). That layer had only an internal audit (run 3a).
- **The deliverable:** **`gate03i-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §3.1 (book pp. 69–73) and §3.3–§3.4 (pp. 77–90).

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
| Under audit | `TCSlib/Cryptography/Asymptotic/{HardCoreLemmas, HardCoreLoops, HardCoreGL, HardCoreGLColl, HardCoreGLFamily, GoldreichLevinDomain, HardCorePermutation, EnsemblesLemmas}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` |
| Context, not under audit | packs 03a–03c's files (whose headlines these files prove) |
| Design record | `briefs/pass-shelat/DESIGN.md` |
| Inventory | `briefs/pass-shelat/inventory-ch3.md`: the proof rows of Thm-87.3 (with .a, .b, .coll), Thm-79.4, Lem-80.5, Cor-81.7, Lem-71.5, Lem-71.6, Lem-73.8 |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

To be filled at the pinned head: elaboration (a fresh replay of the closure); the axiom prints of
the headlines whose proofs live here; admissions (none in these files); lint.

## Specific questions

1. **Goldreich–Levin.** Do the inverter's statements (the majority over pairwise-independent
   samples, the guessing of the `⟨x, r_i⟩`, the success bound) give the theorem at the source's
   strength, with a polynomial loss?
2. **`GoldreichLevinDomain`.** Is the padding of the domain (`|r| = |x|`) handled as the
   collection form needs?
3. **Permutations** (`HardCorePermutation`, `PermFamily.glHalf`, run-3a). Is the hard-core bit of a
   one-way permutation collection stated correctly?
4. **Ensembles.** Do the hybrid and prediction lemmas match their inventory rows, and the concrete
   layer's `predict_eq` (duplication-ledger item DL-5)?

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. The pack closes at **0 blockers and 0 majors**.
