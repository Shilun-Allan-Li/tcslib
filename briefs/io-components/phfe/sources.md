# io-phfe: sources

Prepared 2026-11-18 (records tip `0fec25892d5aea3acde4908d94451f24b3c23b79`). The citation chain the
job must follow is in § 3. What is verified and what is not is marked link by link.

## 1. Obtained

| Tag | Item | Where | SHA-256 | Pages | How used |
|---|---|---|---|---|---|
| [JLS26] | A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026, 30 pp., doi:10.1145/3785007, CC BY 4.0 | maintainer scratchpad `jls26.pdf` (supplied, not downloaded here) | `bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d` (771,518 bytes; PDF created 2026-02-12) | 30 | Full text extracted with `pdftotext -layout`. Read: pp. 1–3, 5 (footnote 3), 7–8 (§1.4), 10–11 (§2–§3), 20–22 (§5), and the reference entries 39, 88, 89, 114, 116, 117, 131, 155. Page images of pp. 7–8 and 20–22 checked |
| [Wee20] landing page | ePrint 2020/1420 abstract page, `https://eprint.iacr.org/2020/1420` | read through WebFetch (a summary by a helper model, not the bytes) | none: no bytes kept | – | Metadata and abstract only (§ 2) |
| [GJLS21] landing page | ePrint 2020/764 abstract page, `https://eprint.iacr.org/2020/764` | read through WebFetch (a summary by a helper model, not the bytes) | none: no bytes kept | – | Metadata and abstract fragments only (§ 2) |

One web search, by the public title of [Wee20], was used to find its ePrint number. No project
detail was sent anywhere.

## 2. Refused (stopped as instructed, no workaround tried)

| URL | Route | Result |
|---|---|---|
| `https://eprint.iacr.org/2020/764.pdf` (GJLS21) | `curl -L` through the configured proxy | proxy tunnel `200 Connection Established`, then **HTTP/2 403** from `server: cloudflare`, header `cf-mitigated: challenge` (a "Just a moment..." JavaScript challenge page, 5,367 bytes, SHA-256 `34c2577f…faec`) |
| `https://eprint.iacr.org/2020/1420.pdf` (Wee20) | `curl -L` through the proxy | the same: **HTTP/2 403**, `cf-mitigated: challenge` (5,391 bytes, SHA-256 `8fde3bf6…cfe9`) |
| `https://eprint.iacr.org/2020/1420.pdf` | WebFetch | **HTTP 403 Forbidden** |
| `https://eprint.iacr.org/2020/764.pdf` | WebFetch | **HTTP 403 Forbidden** |

The challenge pages are kept only in the maintainer scratchpad (`io-phfe-prep/work/refused-*.html`).
`io-phfe-prep/sources/` is empty. The refusal comes from the site's bot challenge, not from the
proxy. A search result also lists an NTT Research copy of [Wee20]; it was **not** fetched, under the
no-workaround rule. **Seyoon (or the maintainer, by hand) must download both PDFs and stage them
on the exchange** at `outbox/io-components/sources/` with a `SHA256SUMS` (README, step 2).

What the landing pages say (helper-model summaries; treat as unverified until the PDFs are read):
- **[Wee20]** H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*, ePrint
  2020/1420, received 2020-11-15, "a minor revision of an IACR publication in TCC 2020", CC BY 4.0.
  Abstract: public-key FE for quadratic functions; a **public-key partially hiding FE** supporting
  **NC¹ computation on public attributes and quadratic computation on the private message**, with
  ciphertext size independent of the public attribute's length; **selective, simulation-based
  security against unbounded collusions**; from the **(bilateral) k-Lin assumption in prime-order
  bilinear groups**; core technique: a reduction from FE for quadratic functions to FE for linear
  functions. TCC 2020, LNCS 12550, pp. 210–228, doi:10.1007/978-3-030-64375-1_8 ([JLS26, ref. 155]).
- **[GJLS21]** R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*, ePrint
  2020/764, received 2020-06-24, last of 4 revisions 2025-01-03, "a minor revision of an IACR
  publication in EUROCRYPT 2021" (LNCS 12698, pp. 97–126; [JLS26, refs. 88, 89]). Abstract:
  partially hiding **public-key** FE for **degree-2 functions on the secret part** and **arithmetic
  NC¹ on the public part**, "assuming only standard assumptions over asymmetric pairing groups".

## 3. The citation chain (Seyoon's directive of 2026-11-18)

**(a) JLS26 → GJLS21. Verified from the JLS26 PDF.**
- [JLS26, Theorem 5.1, p. 21] is "(Theorem 10.3 and Theorem 10.4 [88])", [88] = GJLS21 ePrint
  2020/764 (2020). Hypotheses: constants τ ∈ (0, ∞), ε ∈ (0, 1), d ∈ ℕ; λ the security parameter,
  p a λ-bit prime, k a large enough polynomial in λ; sub-exponential security of
  (i) **Bilateral-DLIN on asymmetric bilinear groups of order p "(implied by the DLIN assumption on
  symmetric bilinear groups of order p)"**, (ii) LWE over ℤ_p with sub-exponential modulus-to-noise
  ratio 2^{k^ε}, (iii) an sPRG with stretch 1 + τ and complexity (deg d, deg 2) over ℤ_p
  (Definition 3.1). Conclusion: sub-exponentially secure iO; with polynomial security, compact FE for
  all circuits. [JLS26, Theorem 5.2, pp. 21–22] composes it with Theorem 4.1.
- [JLS26, §1.4, pp. 7–8]: DLIN on symmetric groups "could be replaced by the SXDH assumption over
  asymmetric bilinear pairing groups, which was used in the conference version [116]. Both
  assumptions are used for constructing a tool called Partially Hiding Functional Encryption
  (PHFE), for constant degree public computation and degree 2 private computation. A slight
  difference is DLIN directly gives public key PHFE scheme by the work of [155], while SXDH gives
  secret key PHFE [114, 131]."
- [JLS26, §1.1, p. 3]: DLIN: for a λ-bit prime p, groups G, G_T of order p with an efficiently
  computable non-trivial symmetric bilinear map e : G × G → G_T and a canonical generator g,
  `(g^x, g^y, g^{xr}, g^{ys}, g^{r+s}) ≈_c (g^x, g^y, g^{xr}, g^{ys}, g^z)`, x, y, r, s, z ← ℤ_p;
  introduced by Boneh–Boyen–Shacham [JLS26, ref. 39] (CRYPTO 2004, LNCS 3152, pp. 41–55).
- [JLS26, Definition 3.3, p. 10]: sPRG ∈ (C, deg d) over ℤ_p (p = p(λ) efficiently computable): for
  each index I there are Process_I ∈ C and an m(n)-tuple Q_I with `Eval(I, sd) = Q_I(P̄, S)`,
  `P̄ = Process_I(P)`, Q_I of degree 1 in P̄ and degree d in S. For (deg d, deg 2): Process_I is
  degree d in the public seed and Q_I is degree 2 in the private seed.
- **Not in JLS26:** any definition of PHFE, any theorem about it, or any GJLS21 definition number.
  PHFE is consumed inside [GJLS21]'s proofs of Theorems 10.3/10.4, which JLS26 cites without
  restating them. JLS26 does not say which ePrint revision of [88] its numbers refer to. Its
  footnote 3 (p. 5) says [88] was updated after JLS formalized sPRGs, so the numbering is that of
  a later revision; check it against the latest one (2025-01-03) first.

**(b) GJLS21's PHFE definition. NOT pinned (PDF refused).** Unknown: the definition number; the
syntax; whether Theorems 10.3/10.4 use the public-key form; the exact function class; correctness
(value or "in the exponent"); the security notion (simulation or indistinguishability, selective or
adaptive, the number of keys and ciphertexts, any semi-functional or "1-key 1-ciphertext" form); the
compactness required. Abstract only: public-key, degree 2 on the secret part, arithmetic NC¹ on the
public part, asymmetric pairing groups. These are design-r1 questions **Q1–Q4**, not guesses.

**(c) Wee20's scheme and theorem. Abstract-level only (PDF refused).** Public-key; NC¹ public ×
quadratic private, f(x, z) with z private; selective simulation security with unbounded collusions;
bilateral k-Lin in prime-order (asymmetric) groups. Theorem and section numbers: **not obtained**.
Known gaps against the JLS26 pipeline, before reading the PDF:
- *group setting:* asymmetric bilateral k-Lin vs. symmetric DLIN. JLS26's own adaptation (Theorem
  5.1's parenthetical; §1.4) bridges it: run the scheme with G₁ = G₂ = G, k = 2, and bilateral
  2-Lin becomes DLIN in G. Cite [JLS26, Thm 5.1 and §1.4] for the adaptation (ruled 2026-11-18);
- *function class:* NC¹ in Wee20 vs. constant degree in JLS26 §1.4: JLS26's class is a subclass;
- *security notion:* match against (b) once GJLS21 is read. If it differs, the design's bridge rule
  applies (design-r1 § 1.3).

## 4. Citations for the Lean docstrings

Every location the job writes is checked in the staged PDF. None is copied from this file without
checking. Tags:
- `[JLS26, §1.1]` (DLIN, p. 3), `[JLS26, §1.4]` (PHFE from DLIN, pp. 7–8), `[JLS26, Definition 3.3]`
  (complexity classes), `[JLS26, Theorem 5.1]` (the consumer, p. 21).
- `[GJLS21, Definition <N>]` for the PHFE notion; `[GJLS21, Theorems 10.3, 10.4]` for its use. `<N>`
  is the placeholder `<GJLS21-PHFE-DEF>` in the dispatch prompt.
- `[Wee20, <§/Theorem>]` for the scheme and its security, from the staged ePrint 2020/1420.
- `[BBS04]` for DLIN's origin, through JLS26 (no BBS04 PDF; do not invent a location).
- Library precedents: `[BB04]` and `[PS10]` as in `Pairing/*` and `IdentityBased/*`.

Policy §2 ingest: as the pairing campaign's Q12(A), keep the PDFs uncommitted, staged on the
exchange only. The job adds nothing under `blueprint/`.
