# Gate06 primary sources: round-1 access and version manifest

**Round 1: common preparation complete; ready for staging (2026-11-07).**
Audit source: `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`; checked comparison ancestor:
`eee107e92a7db11f1f8c98a5c2867304f57ddc54`; draft PR #232. Common results are in `PLAN.md` and
`briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/FINAL-EVIDENCE.md`: 54 math modules plus seven facades; 37 source-seal passes and 17 failures
(138 diagnostics/110 unchanged blocks), all 11 controls, 2,881 axiom identities with 46
admitted-dependent names, and three retained legacy C3 pairs. No external gate closure,
whole-source pass, receiving-auditor access or actual staging/dispatch is attested here.

The source-recovery verification recorded below used `pdftotext -layout` and `pdfinfo` to read
files as data. That source-recovery pass performed no Lean/cache/apps, Git mutations, source
edits or external staging. All recovered third-party PDF copies remain under the ignored integration-worktree
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
The exact PS10 campaign copy is tracked as `Pass–Shelat.pdf` at the frozen source commit;
retrieve it from that Git snapshot or its [raw file](https://raw.githubusercontent.com/Shilun-Allan-Li/tcslib/3f6db40e1688c4a0bb922c9575dd3bd2157a650b/Pass%E2%80%93Shelat.pdf) and verify the hash above. This identifies the delivered repository copy; it does not assert the receiving auditor has already accessed it.

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

## Round 1 access responsibilities and remaining comparison limits

All named Goldreich sections and PSV numbered statements requested in source recovery are
locatable in the recorded primary author copies. The round-1 source metadata preserves their
exact author-version labels, URLs, hashes and pagination limits. The PSV full-version proofs
remain unavailable; author-copy/publisher-copy equivalence is not certified. KV94/SSBD14/Gar26
remain earlier gated/contextual source uses and were not freshly re-reviewed in source recovery.

The common PS10 reference is the provided exact tracked `Pass–Shelat.pdf` copy identified above;
receiving auditors verify its bytes/access through that provided copy or the revision-qualified
repository link. Use the official Goldreich/PSV URLs for legitimate personal retrieval, and
verify access before the corresponding comparison. Each Codex auditor must report exact
unavailable comparisons in the findings Markdown returned in its audit chat. Unavailable
comparisons do not become blanket source-fidelity approval. No recovered third-party PDFs,
full-text extractions or rendered pages are redistributed in the source/records/exchange packs.

The four round-1 packs preserve strict-PPT aborting versus expected-time simulation, draft
versus published pagination, enhanced inversion versus the formal Boolean predicate, and the
PSV06 copy-to-bottom versus PSV07 COPY convention. These are mathematical audit subjects,
not additional rulings or conclusions certified by this access manifest.

Source-only bundle/manifests and completed common evidence are recorded in `PLAN.md` and
`briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/FINAL-EVIDENCE.md`. The final records commit, records/common archive hashes and final-index hash
are pinned externally in the staged exchange READMEs and user dispatch prompts; no self-hash
or future commit attestation is embedded here. The user dispatches all four Codex audits after
reviewed staging; the audits may run in parallel, and each prong's fills follow its own gate
closure. The S2 candidate-host fill is not incorporated or attested by this Gate06 source.

**Not yet clear to merge — external statement audits, source comparisons and their resolutions remain.**
