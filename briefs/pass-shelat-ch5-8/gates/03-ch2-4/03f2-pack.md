# Gate 03f2 ([PS10] ch. 2–4, factoring, RSA, Rabin; number theory): external statement audit pack

**Status: ready to dispatch once [Shilun-Allan-Li/tcslib#201](https://github.com/Shilun-Allan-Li/tcslib/pull/201) merges** (re-staged 2026-11-05 at that PR's head, the gate 03a + 03c repairs; first staged at `a3c5fa8b`; the evidence is under `evidence/f2/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`0c348ff94cacf24d96d99078c9dd9e328530c8d2` (the head of #201; its Lean files are what the branch holds once #201 merges). This pack covers the factoring assumption and the factoring-based candidates (the weak one-way function `f_mult`, the factoring collection, RSA and Rabin with their trapdoors), and the number theory they rest on (Euclid, modular exponentiation, groups, primality testing, quadratic residues, the density of primes).
- **This pack gates fills.** Its files hold **36 `sorry`s**, to be filled after this pack
  closes (user's ruling of 2026-11-05). A statement that cannot be proved as stated, or that is
  weaker than the source, must be found **now**.
- **Gate type:** an external **statement gate** (`workflow.md` §3), over a layer written in another
  campaign (Frederick Dehmel's, now closed). That layer had only an internal audit (run 3a).
- **The deliverable:** **`gate03f2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §2.3 (book pp. 29–33), the factoring statements of §2.4 (Thms 33.5 and 36.3), and §2.6–§2.12 (pp. 41–63).

## Changes since the first staging (repairs of the interface packs; check them, do not re-find them)

The pin moved from `a3c5fa8b` to the head of the gate 03a + 03c repair PR. Changes in or near this pack's files:
- **G3-1** (gate 03b major, merged in #198): `Collection` gained the field `encD_decD`, which makes decoding canonical. The proofs:
  - the distinct-primes collection: `encodeDistinctPrimes_of_decode` (`Concrete.lean`, context);
  - `rsaTrapdoor`: `rsaEnc_of_rsaDec`, which covers the invalid-index branch (the canonical string of `1 mod N`);
  - Rabin's and Blum's collections: inline proofs.

  They rest on the numeral lemmas `natToList_length_listToNat` and `natToList_val_natCast` (`Arithmetic.lean`).
- **Gate 03l, major 1:** the axiom attestation below prints every public theorem and lemma of this pack's files, not only `Checks.lean`'s headlines.

## Brief for the auditor

Pack 03a's brief applies unchanged (its pack is in the bundle). Also, for **every sorried
declaration**, say whether it is (a) true as stated and provable from the hypotheses it carries,
(b) true but weaker than the source, or (c) false or unprovable as stated. For (c), give a
counterexample or the missing hypothesis. Attempt at least **three adversarial instantiations**,
for example:
- a "Blum integer" generator whose primes are equal with non-negligible probability;
- a weak one-way function whose failure probability is not noticeable at some lengths;
- a Rabin inverter that uses its advice to know a square root of `-1`.

Check the run-3a repairs in scope instead of re-finding them. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/Candidates/{Factoring, RSA, Rabin}.lean`, `TCSlib/Cryptography/NumberTheory/{Chebyshev, Euclid, ModExp, Primality, QuadraticResidues, Units}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (for its brief and severity guide) |
| Context, not under audit | `Candidates/Arithmetic.lean` (pack 03b); the files of packs 03a–03d |
| Design record | `briefs/pass-shelat/DESIGN.md` (§1 D11 (the arithmetic hypothesis bundle) and the open questions on Rabin/RSA scope; §5 the deviations register; §7 the source's errors and gaps) |
| Inventory | `briefs/pass-shelat/inventory-ch2.md`: Def-29.1, Asm-30.1, Thm-33.5, Alg-33.6, Claim-34.1, Thm-36.3, Alg-37.4, Thm-51.1, Asm-53.1, Thm-53.2, Thm-55.2, Alg-55.3, Thm-57.2, Thm-61.7, Thm-61.8, Alg-62.9, Thm-63.10; the `NumberTheory/` rows Def-29.3 to Claim-63.1 (33 rows) |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the discrete-log candidates (pack 03f1) |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `0c348ff94cacf24d96d99078c9dd9e328530c8d2` (evidence under `evidence/f2/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 73 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   54 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 230 prints of every public theorem and lemma in this pack's files:
   177 use only the standard axioms, and 53 depend on `sorryAx`; any other axiom is listed
   in the log.
3. **Admissions** (`admissions.txt`): 36 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 10 files.

The replay is the 416-module replay at `af91d53a` overlaid with the re-check of the 98 modules
downstream of #201's changes at its head (`evidence-repairs/03ac/replay.log`); each line of
`replay.log` is the newest check of its module. The closure is smaller than at the first staging
because 03a's repair narrowed facade imports (`Randomized` → its three files).

Pack-specific notes (as drafted):
- elaboration (a fresh replay of the closure);
- the axiom prints of every public theorem and lemma of this pack's files;
- admissions: the 36 `sorry`s, listed by declaration;
- lint.

## Specific questions

1. **The factoring assumption (Asm 30.1) and `f_mult` (Thms 33.5, 36.3).**
   - Is the assumption on the right distribution: two independent uniform `n`-bit primes?
   - Is `f_mult` weakly one-way at the source's strength, with the density of primes
     (Chebyshev, Thm 31.3) as the only non-trivial input?
2. **The collections (Thm 51.1; RSA Thms 53.2, 55.2, 57.2; Rabin Thms 61.7, 61.8, 63.10).**
   - Are the samplers' specifications and closeness statements what `Collection` requires?
   - Is "RSA hardness implies factoring hardness" the right direction? Is "Rabin is as hard as
     factoring" stated for Blum integers, as decided (open question 3: `p ≠ q`, Blum integers,
     the density of primes `≡ 3 (mod 4)` as an explicit hypothesis of Thm 63.10's `Gen`)?
3. **The trapdoors** (`rsaInv_spec`, `blumInv_spec`). Is inversion with the trapdoor correct on
   every sampled index?
4. **Number theory.**
   - Are Euclid, modular exponentiation and the Miller–Rabin test stated with correct
     complexity and error bounds (Thm 49.14; Lem 50.15a/b)?
   - Run 3a deferred two minors here: P6-1, the oddness in Lemma 50.15, and Lemma 50.15b. Are
     they still minor?
5. **Sorried statements.** All 36 are in the three candidate files. Give each a sorry verdict
     (a / b / c).

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. Add the column **Sorry verdict** (a / b / c, see the
brief) for sorried declarations. The pack closes at **0 blockers and 0 majors**.
