# M5 raw security / subexponential proof preparation

Seven unelaborated replacement bodies cover the existing M5 Security.lean stubs.
No Lean, Lake, build, cache, exact?, apply?, axiom, or implementation-source edit was
performed. Existing Security.lean statements and all advice/realiser quantifiers
remain unchanged. Each tactic candidate has one outer by and no nested tactic block;
the two joint-conclusion candidates are tactic-free terms.

The candidate source statement snapshot has Security.lean SHA256
`1d4ea88eede96184453c6e160527f950778fb062f2ae3239acfe4e02eea9f857`.
The lead's intervening Samplers proof repair changes no Security statement. Exact
current HEAD is recorded in static-checks.json; source content, not a stale HEAD
label in historical notes, binds these proof goals.

| Existing theorem | Body candidate | Necessary already-proved inputs before validation |
| --- | --- | --- |
| `jls_secure` | negligible/01-jls_secure.proof | prop41, Params.claim42, Params.le_n; the supplied assumptions/realisability and existing public readers. |
| `jls_subexpSmall` | subexp/01-jls_subexpSmall.proof | prop41, Params.claim42, Params.D_pos; fixed positive input exponents and all-adversary shared SubexpSmall hypotheses. |
| `jls_subexpSecure` | subexp/02-jls_subexpSecure.proof | jls_subexpSmall and Params.D_pos actually proved; shared SubexpHard readers. |
| `theorem41` | closing/01-theorem41.proof | jls_secure, jls_hasComplexity, jls_hasPolyStretch actually proved. |
| `theorem41_subexp` | closing/02-theorem41_subexp.proof | jls_subexpSecure plus the same complexity/stretch inputs actually proved. |
| `exists_sprg_raw` | closing/03-exists_sprg_raw.proof | theorem41 actually proved; select E=max1 E0 and instantiate the supplied own-family hypotheses. |
| `exists_sprg_raw_subexp` | closing/04-exists_sprg_raw_subexp.proof | theorem41_subexp actually proved; same parameter/family selection. |

A green elaboration against the current unresolved prerequisites would not validate
these theorems. The lead must check the resulting dependency/axiom graph after M1-M4
and M2/M3 prerequisites are filled. No candidate treats an existing sorry body as
search evidence, or proves a theorem by itself/downstream consequences.

Only shared Foundations.Negligible / Foundations.Subexponential APIs are used for
asymptotic steps. The own realization/assumption/security equations are read through
published iff/equation readers, and RealizesOn itself is never unfolded. No local
negligible/subexponential/realisation variant or machine/sampler value is constructed.
See negligible-reuse.md and fixed-exponent.md for exact public API locations and
quantifier/dependency reasoning.

Remaining mechanical risks are implicit-reader arguments, associating the three
majorant terms, rewriting natural-cast power schedules under both sides of a bound,
and the local Params constructor's definitional projections in existence bodies.
These are precisely why the candidates are marked untested; no statement repair is
proposed and no extra assumption was inserted.
