# HashAndSign: one proof-repair proposal

Proposal only. No library source was edited and no Lean/cache/Git command was run.
The initial-survey source remains frozen at
`e9d64158461bfe24ddc88ab885bc4017899b4c16`.

Source: `TCSlib/Cryptography/Authentication/HashAndSign.lean`, SHA256
`3cf353234d367d3526b2a76ecb1e45448540cb1082041771b3d8a9ccdfa719bd`.

Evidence: records checkout,
`briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/`,
`runs/G06Seal_008_TCSlib_Cryptography_Authentication_HashAndSign.log` and
`seal-manifest.json` (ordinal 8).

The harness installed and verified all 1371 requested names: 1353 active and
18 already irreducible. Its EOF verifier checked all 1371. The run completed
with RC 1 and source errors, rather than a harness-installation failure.

## Diagnostic mapping and root causes

The log contains six ordinary `error:` messages plus one
`error(lean.unknownIdentifier):` message. Overlapping context excerpts must not
be counted as additional diagnostics. The manifest maps them as follows.

| Probe position | Source position | Classification |
| --- | --- | --- |
| 1683:39 | 250:39 | Root: `runAt_hsGen` header applies `rho` to `Fin.natAdd ...`, whose sum length is not definitionally the sealed `(hsGen S H).coinLen n`. |
| 1696:58 | 263:58 | Root: `runAt_hsSign` header passes `r : S.sign.Coins n` directly to `(hsSign S H).runAt`, which requires `(hsSign S H).Coins n`. |
| 1697:85 | 264:85 | Cascade from that ill-typed signing header; the displayed `List.ofFn sorry` is elaborator recovery, not an added source admission. |
| 1719:8 | 286:8 | Cascade: `runAt_hsGen` was not successfully declared, so the correctness proof cannot rewrite with it. |
| 1717:13 | 284:13 | Correctness remains open after that failed rewrite. Further coin-transport work in this block is also visible statically; see below. |
| 1799:40 | 366:40 | Independent root: `hn` ends at `n`, while `hashAndSign` requires the sealed Lamport scheme's evaluated message length. |
| 1800:55 | 367:55 | Same independent root at the security-theorem application. |

`hsGen` and `hsSign` are same-file abbreviations, so their notation bodies may
reduce. Their enclosing `NUPPT.coinLen` and `NUPPT.ofPolyTimeUniform` ordinary
definitions are foreign and sealed. The two header failures occur before the
respective `:= by`; changing only those proof bodies cannot make the current
literal headers well typed under this seal. No reducibility override or seal
weakening is proposed.

## The single proposed repair

`HashAndSign-exists-lamport-msgLen.patch` changes only the existing term proof
of `exists_oneTimeSecure_of_crh_owf` (source 366-368). It introduces a local
proof `hlen` of the actual length premise. Its chain is:

1. `lamport_msgLen L f E hE hfE` gives the message-length polynomial `.var`.
2. `congrArg (fun p : PolyExpr => p.eval n)` and `PolyExpr.eval_var n` give
   `(lamport L f E hE hfE).msgLen.eval n = n`.
3. Reverse that equation and compose it with `hn n`.
4. Supply the same `hlen` to both uses of hash-and-sign, and use the existing
   public `hashAndSign_msgLen` equation for the existential's length field.

Relevant public declarations already in source:

- `Lamport.lean:529`: `lamport_msgLen : (lamport L f E hE hfE).msgLen = .var`.
- `Randomized/PolyExpr.lean:114`: `eval_var (n) : .var.eval n = n`.
- `HashAndSign.lean:304`: `hashAndSign_msgLen H S hlen`.

The proposal adds no tactic block, declaration, helper definition, or admission.
It preserves every theorem header and every construction data field. It is not
claimed to repair the entire file. The patch is statically matched against the
frozen source, but has not been elaborated.

## Remaining work, without further proof proposals this invocation

- `runAt_hsGen`, source 244-258: its header needs an explicit typed coin
  transport (or an equivalent public list-coin statement), before its proof can
  be repaired. The required length equation is
  `(hsGen S H).coinLen n = S.gen.coinLen n + H.gen.coinLen n`; the existing public
  `NUPPT.coinLen_eq`, `NUPPT.coins_ofPolyTimeUniform`, and `PolyExpr.eval_add`
  expose it. `List.ofFn_congr` preserves the transported tape, and the existing
  `ofFn_coins_split` then supplies its two segments. This is an interface repair,
  not evidence that the intended generator equation is false.
- `runAt_hsSign`, source 261-267: its header needs a transport from the original
  signer's coins to the wrapper's coins. `NUPPT.coins_ofPolyTimeUniform` supplies
  the polynomial equality; `NUPPT.coinsCongr` and
  `NUPPT.coinsCongr_ofFn` are already public. Alternatively, a list-coin run
  equation avoids identifying the two function types in the header. Its
  intended payload equation is unchanged.
- `hashAndSign.correct`, source 284-301: after usable run equations exist, the
  raw generator segments at 290 and 292 still require the same length
  transport. `rs : (hsSign S H).Coins n` at 301 must also be transported to
  `S.sign.Coins n` before applying `S.correct`. These are statically visible
  dependencies, not additional counted diagnostics from this run.

Root should apply and check the chosen patch later, then assess the remaining
header/interface repairs separately. Initial log, manifest, probe sources,
builder, and frozen library bytes are unchanged.
