# Components of indistinguishability obfuscation (JLS)

## Scope and ownership

Seyoon approved this campaign on 2026-11-18 (decision log, first row). It formalizes two of the
inputs to the iO construction of Jain–Lin–Sahai [JLS26, Theorem 5.1, via GJLS21]. It runs as an
experiment: **each component is one end-to-end Codex job** (statements and proofs in a single
delivery, without intermediate maintainer steps), **gated twice**: a statements gate on the job's
statements-only commit, then a proofs gate on the finished delivery.

1. **Structured-seed PRG (sPRG)** [JLS26, §3–§4, Theorem 4.1]: definitions of LPN over 𝔽_p
   (Def 2.3), Boolean PRGs with locality and multilinear degree (Def 3.4), and sPRGs with
   complexity (deg d, deg 2) (Defs 3.1–3.3); the construction, its stretch (Claim 4.1) and its
   pseudorandomness (Proposition 4.1, Lemma 4.2, Claim 4.2).
2. **Degree-2 partially hiding FE (PHFE)** from DLIN on symmetric bilinear groups [Wee20, cited as
   [155] in JLS26 §1.4]: the definitions and the public-key scheme with its security.

**Security convention (Seyoon, 2026-11-18):** non-uniform PPT throughout, the library's convention
(`LWE.DLWEAssumption`, `Pairing` assumptions; [PS10, Definition 26.8]). Every reduction is a
machine construction.

**Out of scope:** FE ⇒ iO bootstrapping (AJ15/BV15), the bilateral-DLIN/LWE steps of GJLS21,
NC⁰ PRGs from random local functions, OWF ⇒ PRG (deferred until cleanup Stage 2 merges). The
link "an ordinary PRG is an sPRG" (JLS26 Def 3.4) to `Pseudorandom/Generators/Asymptotic/Defs`
waits for Stage 2 (S2-B owns that file).

**Home and binding rules.** Records (this file, `briefs/io-components/`) live on the records branch
`cryptography/pass-shelat-ch2-4` and are pushed by the maintainer. Lean reaches that branch only by
PR, opened by the maintainer and merged by Seyoon. Binding: `policy.md`, `workflow.md`,
`briefs/pass-shelat-ch5-8/CLAUDE.md` and `MAINTAINER-HANDOFF.md` §2, the duplication rule.

## Deferred library work

**Generic sampler bridge (Seyoon, 2026-11-18; to formulate later, reusable across campaigns).** The
current convention states non-dyadic laws (uniform ℤ_p for prime p, LPN and LWE noise) as exact finite
distributions, with samplers as separate contracts (as `LWE.Family` does). Wanted later: one generic
bridge saying such laws can be instantiated from fair coins **while keeping perfect correctness**.
Seyoon's sketch: draw x uniformly from [0, M) with M = 2^k much larger than the domain size N; map the
first q·N values (q = ⌊M/N⌋) onto the domain in equal-size buckets, so the output is exactly uniform
given success; if x lands in the leftover M − q·N values, the algorithm "gives up" by a fallback that
keeps correctness exact (e.g. sends things in the clear). Failure has probability < N/M, so security
changes by at most that statistical distance, which is negligible for k large enough. Rational laws
such as Bernoulli(ℓ^{−δ}) fit the same pattern with weighted buckets. To decide later: the reusable
statement (per sampler or per experiment, how fallbacks are specified, how the failure probabilities
are summed), and a duplication check against the existing ℤ_p and noise samplers in `Pairing/`,
`LWE/` and `Games/`.

## References
* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded
  Assumptions*, J. ACM 73(1), Article 1, February 2026 (CC BY 4.0).
* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*, TCC 2020.
* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems*, EUROCRYPT 2021 (ePrint 2020/764).

## Decision log

| Date | Decision / evidence | Status |
|---|---|---|
| 2026-11-18 | **Campaign opened (Seyoon).** Two end-to-end Codex jobs, each gated separately on statements and on proofs: (1) the JLS26 §4 structured-seed PRG, (2) degree-2 PHFE from DLIN [Wee20]. Security: non-uniform PPT throughout (ruled for the sPRG; the library convention, applied to PHFE too). Maintainer assessment before the ruling: the sPRG is the one component JLS26 proves in full, is independent of cleanup Stage 2 (only additive Games touches), and is ~4–7k lines; PHFE is second (source to ingest; definition-heavy; Stage 2 touches `Pairing/Assumptions` in one proof-level row); OWF ⇒ PRG (Mazor–Pass) deferred until Stage 2 merges (it builds on OneWay, hard-core/GL, Ensembles, PRG defs, `LeftoverHash`, `Entropy`, all in Stage 2); FE ⇒ iO bootstrapping to be designed with Seyoon, not run end to end. Noted for the statements: parameter rounding (ℓ, B, c, √c), non-dyadic laws (uniform ℤ_p, the LPN noise), the side conditions λ > log n and log n large, and JLS26 p. 14's "degree d+1" vs p. 17 and Thm 4.1's "d" (d appears right). Next: dispatch packs for both jobs. | open |
| 2026-11-18 | **sPRG design inputs (Seyoon).** (1) Parameter rounding (ℓ, B, c, √c, "n a sufficiently large polynomial in λ"): left to the maintainer's judgment. (2) Sampling: state non-dyadic laws as exact finite distributions with samplers as separate contracts, as `LWE.Family` does; a generic sampler bridge keeping perfect correctness is deferred library work (§ "Deferred library work", with Seyoon's bucket-and-give-up sketch). (3) JLS26 p. 14's "degree d+1 in the public seed" is harmless; the statements use d (Theorem 4.1, p. 17), with a docstring note on the discrepancy. | ruled |
