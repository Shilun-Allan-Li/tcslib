# Gate06 primary sources: internal manifest draft

**Status: unissued source-manifest DRAFT (2026-11-07); not staged or dispatched.** The
associated frozen integration source is `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`,
checked comparison ancestor `eee107e92a7db11f1f8c98a5c2867304f57ddc54`; draft PR #232.
Current native/static/style verification and its limits are in `PLAN.md`. The fresh collector
is active; fresh seals, controls and final axiom outcomes are not yet available. This manifest
establishes source-copy identity/access limits, not a gate issue, audit pin or acceptance record.

The source-recovery verification recorded below used `pdftotext -layout` and `pdfinfo` to read
files as data. That source-recovery pass performed no Lean/cache/apps, Git mutations, source
edits or external staging. All PDF copies remain under the ignored integration-worktree
directory `.lake/ps-maintainer/gate06/sources/`. The present record refresh does not assert a
new PDF-content or receiving-auditor access verification.

This manifest supersedes the earlier draft README's missing-file statements for the named
Goldreich and PSV sources. Recovery for personal reading does **not** make the Goldreich PDFs
permissible public-exchange attachments.

## Retrieval identity and provenance

| Local personal-reading file | Primary author URL | Bytes | SHA-256 | PDF pages |
|---|---|---:|---|---:|
| `PSV06-author.pdf` | [Cornell author copy](https://www.cs.cornell.edu/~rafael/papers/PSV06a.pdf) | 294488 | `f5087d68df8782e2ca0465ce511c9dd6778dea70052d666a8ff86bd85873a6e6` | 19 |
| `PSV07-author.pdf` | [Cornell author copy](https://www.cs.cornell.edu/~rafael/papers/newdefs.pdf) | 226230 | `d0d6f5edd2527265d20213b35e2042e018ef7e357049cdd5d379ae1d0938c98e` | 17 |
| `Gol01-ch4-author.pdf` | [Official chapter-4 PDF](https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/part4N.pdf) | 789305 | `97e67c3cae68701705839386a31f462803c6c9e6d1984638442010df99b6f977` | 120 |
| `Gol04-ch7-author.pdf` | [Official chapter-7 PDF](https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/prot.pdf) | 1341448 | `a3ca9c46e62c1764b91eb956b39ebb0d5fb0c61fe149c93a6be9fb3ee149da84` | 204 |
| `Gol04-appendix-author.pdf` | [Official Appendix-C PDF](https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/errI.pdf) | 425995 | `986c2c59a4b9144888ad1e27582ace383e2ee2d52491259975c3f41f76cb79a4` | 42 |

The two PSV files were retrieved by root; their byte counts/hashes were independently checked
against `sources/PSV-retrieval.json`. The three Goldreich PDFs were retrieved from the official
author host with `curl`, following the author's draft index. No third-party book mirror was
used. The directory-index link returned a page-not-found error; the individual official PDF
URLs above succeeded. Initial urllib retrievals reset the connection; they were not treated
as successful downloads. Every retained download has a PDF signature and was readable by
Poppler.

The existing PS10 copies remain identified by SHA-256
`7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`
(1,771,458 bytes). That is the separately recorded course PDF; its book/PDF offset is 12.

## PSV06: cited definition is present

R. Pass, a. shelat and V. Vaikuntanathan, *Construction of a Non-Malleable Encryption Scheme
from Any Semantically Secure One*, CRYPTO 2006, LNCS 4117, pp. 271–289.

| Citation | Location in this author copy | Verification |
|---|---|---|
| Definition 3 | PDF pp. 6–7, §2.2 | The adversary chooses an equal-length message pair after receiving the public key; its challenge-dependent ciphertext vector is decrypted, with challenge copies replaced by `⊥`. The output ensembles must be indistinguishable under CPA. This supports the pack's stated source for the one-challenge `nmGame`. |
| Definition 4 / Theorem 1 | PDF pp. 7–8 | Many-message extension and its equivalence with the one-challenge notion. These are not the relation-based simulation definition. |

The historically uploaded publisher copy had SHA-256
`7b470f4e3f26a56dbfd8956d4f07201ac163cbf716d4c0830b375ac022db8c49`.
**The recovered author PDF is byte-distinct.** Metadata records creation on 2007-01-02, but no
explicit revision identifier was established. Matching title, authors, page count and named
definitions does not establish complete textual identity with the unavailable publisher copy.

## PSV07: numbered equivalences and their proof limit

R. Pass, a. shelat and V. Vaikuntanathan, *Relations Among Notions of Non-Malleability for
Encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535.

| Citation | Author-copy PDF pages | Verification |
|---|---:|---|
| Definition 1, SIM-NME′ | 6–7 | Simulation receives the public key; a bounded message sampler and history function appear. Invalid outputs are allowed. Challenge copying uses a distinguished `copy` value. |
| Definition 2, SIM-NME | 7 | Restricts to non-copying, valid adversaries. |
| Definitions 3–4, IND-NME′ / IND-NME | 8 | The prime version permits invalid/copying outputs; the unprimed version restricts the adversary. |
| Corollary 1 | 9 | SIM-NME′ implies IND-NME′. |
| Theorem 3 | 9 | CPA equivalence of SIM-NME′ and IND-NME′. |
| Theorem 4 | 9 | Strict separation under CCA1/CCA2, even at one message. |

The CPA proof is deferred to a full version; the corollary is tied to another deferred proof.
The recovered PDF does not remove the pack's need to audit the maintainer's arguments.
**Semantic distinction to retain:** PSV06's challenge-copy `⊥` and PSV07's distinguished
`copy` are different conventions; do not describe these definitions as literally identical.

Historical publisher-upload SHA-256:
`c899bf7cff4c8144ac28c31f703d567178f96e31ec9b28d6f4bddf4f337ea57d`.
**The author PDF is byte-distinct.** Metadata names `asiacrypt2007.dvi` and records
2007-12-17 UTC creation/modification; no separate revision label was established. Published-
copy equivalence and availability of a longer proof version remain unverified.

## Goldreich: official draft mapping

The author's [volume-1 page](https://www.wisdom.weizmann.ac.il/~oded/foc-vol1.html),
[volume-2 page](https://www.wisdom.weizmann.ac.il/~oded/foc-vol2.html) and
[draft index](https://www.wisdom.weizmann.ac.il/~oded/foc-drafts.html) establish provenance.
The index labels chapter 4 an early 1998 draft and chapter 7/Appendix C June-2003 drafts.
PDF metadata records June-2014 conversion dates; those dates are not evidence of a 2014
content revision. The published editions are 2001 and 2004. **Draft pagination below is not
a verified published-edition page mapping.**

| Source and cited item | PDF page(s) | Printed draft page(s) | Mapping/result |
|---|---:|---:|---|
| Gol01, Definition 4.3.1 | 16 | 142 | Strict-PPT simulator, failure probability at most 1/2, exact conditional distribution on success. |
| Gol01, §4.3.4 | 27 onward | 153 onward | Auxiliary-input sequential ZK composition. |
| Gol01, Lemma 4.3.9 in this draft | 28 | 154 | Polynomially many independent phases preserve auxiliary-input ZK; also states the perfect case. Phase termination is marked. Do not transfer this draft lemma number to the published edition without checking. |
| Gol04, §7.3.1 / Definitions 7.3.1–7.3.2 | 47–48 | 633–634 | Oracle-aided protocols, sequential oracle calls and privacy reductions. |
| Gol04, Theorem 7.3.3 | 49 | 635 | A private reduction to a privately computable functionality gives private computation in the semi-honest model. The pack's theorem number matches this draft. |
| Gol04, §7.3.2, Construction 7.3.5 / Proposition 7.3.6 in this draft | 52–55 | 638–641 | OT from enhanced trapdoor permutations; the proof explicitly discusses the receiver's sampler coins. |
| Gol04, Appendix C.1 / Definition C.1.1 | 2–3 | 759–760 | Enhanced inversion hardness even given domain-sampler coins. |

The packs retain the following two citation-precision qualifications; preserve them in the issued source/bundle:

- Definition 4.3.1 is the strict-PPT aborting formulation. The liberal expected-time formulation
  is separately numbered 4.3.5 in this draft. Keep the formal retry/truncation bridge and the
  PS10 expected-time deviation distinct; do not attribute expected-time simulation to 4.3.1.
- Appendix C.1.1 defines enhanced **inversion**, not the literal Boolean predicate
  `EnhancedHardCore` used by the formalization. For the OT bit-prediction discussion also cite
  §7.3.2, especially draft pp. 639–641. This supports the source motivation; equivalence with
  the formal predicate is an audit subject, not certified by this manifest.

## Licensing and external-delivery rule

The official [draft notice](https://www.wisdom.weizmann.ac.il/~oded/foc-drafts.html) distinguishes
pre-publication use from post-publication permission. After publication it permits personal
copies without distribution. Accordingly:

- Keep the Goldreich PDFs, extracted full text and any rendered book pages local and ignored.
- **Do not commit, stage, archive into a public exchange pack, or redistribute these book PDF
  copies.** This task does not authorize book excerpts as exchange attachments either.
- External pack metadata may provide the official URLs, citations, hashes and mapping above;
  the external auditor can retrieve the author drafts directly for personal reading or use
  their own legitimate book access. Replace the earlier draft wording that required attaching
  Goldreich PDFs with this link/access arrangement.
- Author hosting of the PSV papers is verified, but no blanket redistribution license was
  established here. Record these as author copies and supply their URLs; do not label them
  the historical publisher uploads or claim a license inferred from public availability.

## Remaining limits and issue-time actions

All named Goldreich sections and PSV numbered statements requested in this review are now
locatable in primary author sources. Remaining source work is precise version/access
disclosure, not a claim that these copies match publisher editions. The full PSV proofs are
still not recovered. KV94/SSBD14/Gar26 were not re-reviewed in this source task.

The current 06B/06C drafts carry these citation qualifications. At issue preserve the author-
version labels, COPY/invalid-output distinction and link-only Goldreich delivery. Record the
receiving auditor's source-access basis or exact unavailable comparisons as
`[ISSUE_SOURCE_ACCESS_DISCLOSURE]`; do not turn unavailable source comparisons into blanket
source-fidelity approval. KV94/SSBD14/Gar26 remain previously gated/contextual source uses,
not fresh access or verification claims here.

The final records commit, bundle/manifest hashes, fresh collector/axiom dispositions and
seal/control outcomes remain the explicit issue-time placeholders in `PLAN.md` and each pack.
This is not an additional mathematical ruling. No external job is prepared or issued by this
manifest; the user's dispatch and the already-required common verification remain separate.

**Not yet clear to merge — receiving-auditor source-access disclosures, fresh verification outcomes and issue-time reconciliation remain.**
