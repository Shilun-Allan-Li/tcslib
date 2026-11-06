# Gate 03j ([PS10] ch. 2–4, GGM, PRF and encryption results): external statement audit pack

**Status: draft.** The pinned head, the attestations and the bundle are filled in once the dedup PR and the F-1 restatement have landed
(`PLAN.md`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`<HEAD, 40 hex, from git rev-parse>`. This pack covers the proof of the GGM theorem (Thm 97.3: a PRG gives a PRF) through the GGM reduction machine, the PRF lemmas, and the proofs of multi-message security of the §3.9 scheme (Thm 99.2) and of the public-key theorems (Thm 104.4).
- **This is a "rest" pack.** Its files mostly hold the proofs of headline theorems stated in
  earlier packs, so its trusted surface is their **auxiliary statements**, definitions and
  sketches. A wrong auxiliary statement can make a proof hold for the wrong reason, or hide a
  weaker result behind a headline.
- **Gate type:** an external **statement gate** (`workflow.md` §3), over a layer written in another
  campaign (Frederick Dehmel's, now closed). That layer had only an internal audit (run 3a).
- **The deliverable:** **`gate03j-findings.md`**, committed as `inbox/gate03j-findings.md` on the exchange branch `exchange/pass-shelat-ch5-8` and pushed (the protocol is that branch's `README.md`: write only that file, `git pull --rebase` before pushing, never force-push, no PR).

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source** is [PS10], 3rd ed., January 2010: `Pass–Shelat.pdf` at the root of `cryptography/pass-shelat-ch2-4` (SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`). Book page = PDF
page − 12. This pack needs §3.8–§3.10 (book pp. 95–105).

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
| Under audit | `TCSlib/Cryptography/Asymptotic/{GGMReduction, GGMReductionEval, PRFLemmas, MultiMessageLemmas, PublicKeyLemmas}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` |
| Context, not under audit | pack 03d's files (whose headlines these files prove), and the concrete GGM proof `Pseudorandom/Functions/GGM.lean` (Garg layer) |
| Design record | `briefs/pass-shelat/DESIGN.md` |
| Inventory | `briefs/pass-shelat/inventory-ch3.md`: the proof rows of Thm-97.3 (and .3), Thm-99.2 (with .1–.3), Thm-104.4 |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (`Pass–Shelat.pdf`, campaign branch root) |
| Standards | `policy.md` |
| Out of scope | tactic proofs |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

To be filled at the pinned head: elaboration (a fresh replay of the closure); the axiom prints of
the headlines whose proofs live here; admissions (none in these files); lint.

## Specific questions

1. **The GGM reduction machine** (`GGMRed`). Does its state loop simulate the hybrid oracle
   exactly on genuine runs? Are the length guards' hypotheses met, not vacuous?
2. **The hybrid argument for GGM.** Is the loss (the depth times the number of queries) as
   stated, and polynomial?
3. **Multi-message security.** Does the bad event (repeated `r`) have the stated bound, and is it
   accounted for in the reduction to PRF security?
4. **Public-key lemmas.** Are the single-bit to many-bit hybrid statements correct?

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. The pack closes at **0 blockers and 0 majors**.
