# Gate 03b ([PS10] ch. 2–4, one-wayness and collections): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/b/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the definitions of one-way functions and of
collections of one-way functions, permutations and trapdoor permutations, and the statements of
the theorems that relate them.
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05),
  over a layer written in another campaign (Frederick Dehmel's, now closed). That layer had only
  an internal audit (run 3a, summary in the bundle).
- **The deliverable:** **`gate03b-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §2.2 (book pp. 26–29), the statements of §2.4 (Theorems 35.1 and 35.2,
pp. 33–35), Remark 33.2, §2.5 (pp. 41–42) and §2.10–§2.11 (pp. 55–57).

## Brief for the auditor

Pack 03a's brief applies unchanged: the trusted surface, the six things to hunt for, the
inventory check, restating every definition in your own words, and 1–3 sentences per theorem.
Attempt at least **three adversarial instantiations**, for example:
- a function family that is one-way for a degenerate reason (empty domain at some lengths,
  outputs that leak the input);
- a collection whose sampler is not efficient;
- a trapdoor that does not invert.

Check the run-3a repairs in scope (pack P3: `Collection.sample_spec`, Thm 42.2, the `1^n` form of
Def 26.1, the canonical default pair) instead of re-finding them. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/Asymptotic/{OneWay, Collections, Permutations}.lean`, `TCSlib/Cryptography/Candidates/Arithmetic.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (in the bundle for its brief and severity guide; its questions are not this pack's) |
| Context, not under audit | pack 03a's files (the machine model, `Negligible`, `Ensemble`, `StatClose`): an earlier pack of this gate |
| Design record | `briefs/pass-shelat/DESIGN.md` (§1 D1–D11, §2.9 and §2.10 the frozen signatures, §5 the deviations register) |
| Inventory | `briefs/pass-shelat/inventory-ch2.md`: Def-26.1, Def-27.3, Def-28.4, Thm-35.1, Thm-35.2, Claim-38.2, Rem-33.2, Def-41.1, Thm-42.2, Def-55.1, Def-56.1 |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` (pack P3) |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the proofs of Thms 35.1 and 42.2 (`OneWayLemmas`, `OneWayYao`, `CollectionsLemmas`), which pack 03h audits for their statements |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/b/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 65 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   17 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 21 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 21 use only the standard axioms, and
   0 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 0 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 4 files.

Pack-specific notes (as drafted):
- elaboration (a fresh replay of the closure);
- the axiom prints for this pack's headline theorems (`audits/pass-shelat/Checks.lean`);
- admissions: none in these four files;
- lint;
- interface use. The declarations cited by ch. 5–8 are:
  - `FunFamily` and `FunFamily.StrongOneWay`;
  - `Collection`, `Collection.HardCore`, `PermCollection` and `TrapdoorCollection`;
  - `Candidates.ArithmeticFP`.

## Specific questions

1. **One-wayness (Defs 26.1, 27.3, 28.4).**
   - Is `FunFamily.StrongOneWay` the source's strong one-wayness: every n.u.p.p.t. inverter given
     `1^n` and `f(x)` succeeds with negligible probability?
   - Is the weak form's "noticeable failure" the source's quantifier order?
   - For worst-case one-wayness, are the `1^n` headline and the literal form `WorstCaseOneWayLit`,
     and the bridges between them, right?
   - What do length-changing functions do to these definitions?
2. **Amplification (Thms 35.1, 35.2; Claim 38.2).** Do the statements say what the source does,
   including the input length of the direct product and the parameters of Claim 38.2?
3. **Collections (Def 41.1, Thm 42.2).**
   - Are the three conditions faithful: efficient sampling of an index, efficient sampling of a
     domain point, and efficient evaluation?
   - The run-3a repair added `sample_spec`, the membership half of Def 41.1 (2). Is that right, and
     is it enough?
   - Is Thm 42.2 stated in both directions at the right strength?
4. **One-way and trapdoor permutations (Defs 55.1, 56.1).**
   - Are "permutation" and "trapdoor" captured: the inversion algorithm with the trapdoor, and
     its correctness on every sampled index?
   - Is the declared deviation "literal `Inv((i, t), y)` not adopted" (P3-5) benign?
5. **`Permutations.lean`.** The permutation sampler uses `permBits n = Nat.size n` and
   `permTrials n = 2n²` (a run-3a repair). Is its failure probability negligible as claimed, and
   are the parameters as stated?
6. **`Candidates/Arithmetic.lean`.**
   - Is the hypothesis bundle `ArithmeticFP` a reasonable stand-in for "these arithmetic operations
     are polynomial-time" (D11; Remark 33.2 on primality)?
   - Is any field stronger than the source's claim, or unsatisfiable?
   - Is any operation missing that the candidates of §2.7–§2.12 need?

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. The pack closes at **0 blockers and 0 majors**.
