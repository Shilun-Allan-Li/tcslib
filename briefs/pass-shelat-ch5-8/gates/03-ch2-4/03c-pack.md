# Gate 03c ([PS10] ch. 2–4, hard-core bits and PRGs): external statement audit pack

**Status: draft.** The pinned head, the attestations and the bundle are filled in once the dedup
PR has landed (`PLAN.md`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`<HEAD, 40 hex, from git rev-parse>`. This pack covers pseudorandom ensembles, next-bit unpredictability, pseudorandom generators and their expansion, and hard-core predicates up to the Goldreich–Levin theorem.
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05),
  over a layer written in another campaign (Frederick Dehmel's, now closed). That layer had only
  an internal audit (run 3a, summary in the bundle).
- **The deliverable:** **`gate03c-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §3.2–§3.4 (book pp. 74–90).

## Brief for the auditor

Pack 03a's brief applies unchanged (its pack is in the bundle): the trusted surface, the six
things to hunt for, the inventory check, restating every definition in your own words, and 1–3
sentences per theorem. Attempt at least **three adversarial instantiations**, for example:
- a "PRG" whose output length is not larger than its seed at some lengths;
- a predicate that is hard-core only because the function is not efficiently computable;
- a next-bit predictor that uses its advice to hard-wire the seed.

Check the run-3a repairs in scope instead of re-finding them. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/Asymptotic/{Pseudorandom, NextBit, HardCore, HardCoreClaims}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (for its brief and severity guide; its questions are not this pack's) |
| Context, not under audit | packs 03a–03b's files (the machine model, ensembles, one-wayness, collections): earlier packs of this gate |
| Design record | `briefs/pass-shelat/DESIGN.md` (§1 D1–D11, §2.12 the frozen definition shapes, §5 the deviations register) |
| Inventory | `briefs/pass-shelat/inventory-ch3.md`: Claim-67.a, Def-74.1, Def-75.2, Rem-75.3, Thm-75.4 (with .conv, .c, .1, .2), Alg-76.5, Def-77.1, Claim-107.c, Constr-77.a, Claim-78.a, Claim-78.b, Def-78.3 (and .coll), Thm-79.4, Claim-79.a, Lem-80.5, Cor-81.7, Constr-82.a, Thm-87.3 (with .a, .b, .coll) |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the proofs of Goldreich–Levin and of the hard-core lemmas (`HardCoreLemmas`, `HardCoreLoops`, `HardCoreGL*`, `GoldreichLevinDomain`, `HardCorePermutation`), whose statements pack 03i audits |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

To be filled at the pinned head:
- elaboration (a fresh replay of the closure);
- the axiom prints for this pack's headline theorems (`audits/pass-shelat/Checks.lean`);
- admissions: none in these four files;
- lint;
- interface use. The declarations cited by ch. 5–8 are `PRG`, `PRG.Secure` and `prg_expand`.

## Specific questions

1. **Pseudorandomness (Def 74.1) and PRGs (Def 77.1).**
   - Is `PRG.Secure` indistinguishability of `G(U_n)` from `U_{ℓ(n)}` against every n.u.p.p.t.
     distinguisher, with `ℓ(n) > n`?
   - Are the length conditions stated for every `n`, or only eventually, and does it matter?
2. **Next-bit unpredictability (Def 75.2, Thm 75.4).**
   - Is the predictor's index `i` chosen as the source has it (adaptively, per `n`)?
   - Are both directions of Thm 75.4 stated, and at what loss?
3. **Expansion (Lem 80.5, Cor 81.7, `prg_expand`).** Does `prg_expand` give any polynomial
   stretch from a one-bit-stretch PRG, with the right composition and the right loss?
4. **Hard-core predicates (Def 78.3 and its collection form; Thm 79.4).**
   - Is "hard-core" stated against n.u.p.p.t. predictors with advantage `1/2 + negl`?
   - Does Thm 79.4 (a one-way permutation with a hard-core bit gives a PRG) need the permutation
     property where it uses it?
5. **Goldreich–Levin (Thm 87.3, the collection form).** Is the hard-core bit `⟨x, r⟩` stated for
   `g(x, r) = (f(x), r)` with `|r| = |x|`, for every strong OWF `f`, at the source's strength?
6. **`HardCoreClaims.lean`** has no inventory row. Say what its declarations claim and whether
   each is true and correctly attributed.

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. The pack closes at **0 blockers and 0 majors**.
