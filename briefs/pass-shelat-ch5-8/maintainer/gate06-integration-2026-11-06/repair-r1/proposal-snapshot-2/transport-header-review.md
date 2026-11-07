# Coin and Fin helper-header transports: independent static review

**Verdict: 0 blockers / 0 majors / 0 minors (static review only).**

Reviewed 11 authorized transport/caller patches against exact frozen commit `e9d64158461bfe24ddc88ab885bc4017899b4c16`,
plus the decoder proposal as an in-memory prerequisite. No new proof was authored and no
library/evidence/Git mutation, Lean/cache command or app was used. Other agents' programs
were read as data only; the reviewer used its own strict unified-diff parser.

## Logical equivalence and all-input coverage

| Scope | Static conclusion |
|---|---|
| HashAndSign generator | `hsGen_coinLen` exactly evaluates its existing sum coin polynomial. `List.ofFn_congr` preserves the full original tape under the new Fin cast; `ofFn_coins_split` reads its original signature-generator prefix and hash-index suffix. No reordering/truncation is introduced. |
| HashAndSign signer/correctness | The published `coinsCongr` equivalence maps original signer coins to wrapper coins; `coinsCongr_ofFn` and `runAt_coinsCongr` preserve the literal activation. Correctness covers every wrapper tape via `e.symm`, with `e.apply_symm_apply` supplying the unchanged input. The message-length cast preserves the exact padded hash word through `List.ofFn_congr` and `ofFn_padFin_eq_padStr`. The Lamport `hlen` witness follows exactly from `hn`, `lamport_msgLen` and `eval_var`. |
| PublicKey `runAt_padEnc` | Changing the binder from original encryptor coins to padded-encryptor coins is a reparameterization by the full bijection `coinsCongr (padEnc_coins ...)`; its RHS uses the same original coin word. `Uniform`, arbitrary argument words and all prior premises remain unchanged. Both `ofPadded` callers pass the transported tape to their original correctness/length assumptions. |
| Yao callA/B headers | The symmetric evaluated OT input equalities cast each original `Fin 2`/`Fin 1` index into the typed input domain. `Fin.cast` preserves its value: Alice's selected key bit and Bob's original input/default lookup are identical. Both casts are invertible; neither adds an input restriction. |
| Typed OT point reader and answers | The new owner reader exactly states `otFunctionality.f`'s selected bit for arbitrary typed inputs and every typed output index. Its output function is constant on the one-bit domain. The same cast expressions match the repaired call headers. `answersB_eq`, singleton flattening and `finProdFinEquiv` preserve call order and `i*n+t`; both prior foreign-body `show` steps are removed. |

All checks include `n=0`. HashAndSign/PublicKey allow empty coin lengths, and also nonzero
constant coin lengths at parameter0; neither needs a bit choice or positivity. Hash word
length0 is covered by the same list equality. Yao's `j : Fin (inB(n)*n)` is empty when n=0;
its answers theorem has `t : Fin n` and is then vacuous. The typed OT owner reader still
covers the fixed two-bit input, one-bit choice/output domains at n=0. Empty `inB(n)` is
similarly vacuous for `i`. Arbitrary malformed/private input and tape words retain their
original `getD` defaults; no extra well-formedness or security assumption is introduced.

## Data, callers and interface discipline

The original string functions, machine abbrevs, construction headers and all data/uniformity
fields before correctness were compared byte-for-byte and remain identical. `yaoHybrid`
and `otFunctionality` data are identical. The transport patches add no helper definition,
change no security game/notion or substantive admission, and add no hypothesis. The separate
decoder prerequisite has its own prior equivalence review.

A read-only `git grep` over **all tracked Lean files at the pinned commit** finds exactly
the two local HashAndSign correctness uses and the two `ofPadded` uses of the modified run
helpers. All are updated. The Yao call helpers have no pinned direct callers; the new answers
patch introduces and covers both, together with the typed OT point reader. Added occurrences
in every scratch proposal patch were checked as data. **No missing repository caller found.**

Every new explicit tactic-list entry inspected is a published equation/lemma or a local
fact. `NUPPT.coinsCongr` remains an opaque interface used through its published word/run
lemmas; no consumer unfolds it. The new `hsGen_coinLen` RHS matches the existing machine
coin sum, and the new OT point reader's RHS matches the owning functionality exactly.
The term `rfl` in the OT owner and call readers needs only owning definitions and permitted
Core `Fin.cast` value projection reduction. Policy §1.10 at lines69–70 explicitly allows
Core/Mathlib reduction in `rfl`/`decide`/`show`; no such definition is newly put in a tactic
unfold/rewrite list. `PolyExpr.eval` is also the recorded approved notation exclusion, and
the statement casts nevertheless use its public constant-evaluation equations.

**No necessary foreign ordinary TCSlib body read is visible in these transport proposals.**
This is a static assessment: native elaboration and sealed replay must still verify it.

## Reproducibility and limits

All patch hunk counts and unique contexts validated, and the four source groups composed
in the recorded order entirely in memory. The HashAndSign patches find shifted contexts
after earlier additions; the PublicKey caller patches are based after its helper change;
the Yao call/answer patches are based after codec delegation. No patch-hunk metadata defect
was found. Original and resulting admission counts match for every group.

No Lean/cache/native run was made in this review. In particular, type elaboration of the
new helper headers and owner term reader, rewrite matching across typed OT indices, and
sealed proofs remain root-owned verification. Source review is not an implicit-read seal
certificate. This verdict does not claim a passing Gate06 or that substantive security
admissions have been filled.

| Source group | Frozen SHA-256 | Composed SHA-256 |
|---|---|---|
| TCSlib/Cryptography/Authentication/HashAndSign.lean | `3cf353234d367d3526b2a76ecb1e45448540cb1082041771b3d8a9ccdfa719bd` | `c333e65b4874978780fb468a42982cc4d6ef6a73d7c6cf6f6a36faaccc7ec379` |
| TCSlib/Cryptography/Composability/PublicKey.lean | `8bc99296a28985a783285c42db1bc0e27787538e78d3c909bbff594dc0ef9717` | `8bae0ef1abea902f1c99bd0979932d48b1b8169ff4281b19bef8cdf30a863dc9` |
| TCSlib/Cryptography/SecureComputation/Yao.lean | `d7d42232e9b74a02c2c24db0df85daa53f2b0c3e310f6e5e1afa7620441c3310` | `07a706e5ab0e535adf90b8e9508422897fff7bf2c3ae4e1f9f9eef29fe919e8a` |
| TCSlib/Cryptography/SecureComputation/Defs.lean | `b761c437034a6d808d09357d6d8a4c1a841d332e1e3d12c707d506cd8c996b51` | `b6a86a5b9f0843642cf3d6a9e3ef05cb34cb4081d24c80a5c139f9cbbdc2452b` |

| Reviewed artifact | SHA-256 |
|---|---|
| HashAndSign-runAt_hsGen-coin-transport.patch | `4787152aec98c9c8397647a30cff0c6288a1ed8be527e56e208e7aa50dd933fb` |
| HashAndSign-runAt_hsSign-coin-transport.patch | `698714417719bec91b768ef2b208465c9cde72fee6d4d6f8acc543c7329379ba` |
| HashAndSign-correct-coin-transport.patch | `1b77738ecbb05dd4d064a8289f902d8487661fcdec53bba29ef219c28e93b722` |
| HashAndSign-exists-lamport-msgLen.patch | `9edc940b0ddf1063dce639afa3368f75addc1d7fc50148acf6ca24b02989b70e` |
| PublicKey-runAt_padEnc-coins-transport.patch | `f7e52d031b254d58ae8047576ed4972d4f4a9fda35b9698e2e0e7a371cd09e0a` |
| PublicKey-ofPadded-correct-coins-transport.patch | `637181610c6bf4996d0270787aebe3f4ca55de5985e5006dbcd218fee0a48318` |
| PublicKey-ofPadded-enc_length-coins-transport.patch | `c89c07f4238068843e9812987f9b03160e778cc5a129aa73473bd184a05561ae` |
| Yao-decodeMsgs-delegate-decWords.patch | `df8ad758103ae54ecaa42fdfc5c7ca889665459a1b9437372eeda47e4c18e976` |
| Yao-yaoHybrid_callA-typed-input.patch | `84cb220ccc7c6d7099bee5591354c893f5a2e11fb38a931f77b5b363d0f21a5a` |
| Yao-yaoHybrid_callB-typed-input.patch | `acb5dbebe258635557923797c60569bdc0f6125e6635179ed196ac993ba8b599` |
| Yao-yaoHybrid_answersB_getD-typed-OT.patch | `a4613412cafe9001d416493f854cf0a91f5890de3e2f6ecfb3a1666d142a9ac8` |
| Defs-otFunctionality_f_snd_apply-typed-reader.patch | `6061db3e8cc5dd2113feceda8b46b0626d19216aca6020e229853c15b718476a` |

The companion `transport-header-review.json` records the ordered hunks, source/data checks,
all caller evidence, exact patch fingerprints, owner fingerprints, cases and limits.
