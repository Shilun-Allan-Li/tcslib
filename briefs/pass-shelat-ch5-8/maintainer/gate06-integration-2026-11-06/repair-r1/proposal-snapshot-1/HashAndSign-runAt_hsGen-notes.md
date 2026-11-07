# HashAndSign: explicit generator-coin transport

This is a separate, unapplied proposal against frozen head
`e9d64158461bfe24ddc88ab885bc4017899b4c16` and source SHA256
`3cf353234d367d3526b2a76ecb1e45448540cb1082041771b3d8a9ccdfa719bd`.
No library bytes were changed and no Lean/cache/Git command was run.

Patch: `HashAndSign-runAt_hsGen-coin-transport.patch`.
It does not include the earlier independent Lamport-corollary proposal.

## Scope and preserved equation

The sole existing tactic block changed is `runAt_hsGen` (frozen source 244-258).
Its arguments are unchanged and it gains no hypothesis. Its right-hand side
still pairs the public/secret signature keys with the hash index, with the
signature generator's coin segment first and the hash generator's segment
second.

The explicit transport fixes the source 250 header error in the initial seal.
The original header tried to apply
`rho : Fin ((hsGen S H).coinLen n) -> Bool` directly to a `Fin` of the component
sum. Under the seal those lengths are propositionally, rather than
definitionally, equal.

The revised statement binds a local tape `sigma` of type
`Fin (S.gen.coinLen n + H.gen.coinLen n) -> Bool`, with
`sigma j = rho (Fin.cast (hsGen_coinLen S H n).symm j)`, before stating the same
two component runs. It explicitly specifies both `Fin.castAdd` and `Fin.natAdd`
lengths. The transport does not reorder or change bits: `List.ofFn_congr`
proves that the original and transported tape lists coincide.

No `hsGen_coins` declaration exists in this frozen library or the previously
saved repairs. The proposal therefore adds the needed owner-side
`hsGen_coinLen` reader beside `hsGen`, with a formula docstring and a term proof
(no additional tactic block). Its exact type is:

`hsGen_coinLen (S : SignatureScheme) (H : CRH) (n : Nat) :`
`  (hsGen S H).coinLen n = S.gen.coinLen n + H.gen.coinLen n`.

The proof composes the public `NUPPT.coinLen_eq`, the constructor's
`NUPPT.coins_ofPolyTimeUniform`, `PolyExpr.eval_add`, and the reverse component
`coinLen_eq` equations. Only the same-file `hsGen` abbreviation is notation;
no foreign ordinary definition is read through its body.

## The one proof block

The proposed proof repeats the same local transported tape, derives
`List.ofFn rho = List.ofFn sigma` by `List.ofFn_congr`, and applies the existing
`ofFn_coins_split` to `sigma`. The final simplification uses only published
equations:

- `NUPPT.runAt_eq`, `NUPPT.runAtL_ofPolyTimeUniform`;
- `S.gen_uniform.runAtL_eq`, `H.gen_uniform.runAtL_eq`;
- owner readers `hsGenFun_eq`, `hsSigKey_eq`, `hsIdx_eq`;
- `NUPPT.inParam_eq`, `inCoins_eq`, `advInput_eq`, `layout_eq`;
- the pairing projection equations and `List.length_replicate`;
- the reverse signature-generator `coinLen_eq`, the tape equality and the
  two split equations.

The existing `ofFn_coins_split` handles either component length being zero;
there is no positivity premise. No host, helper definition, `simp` attribute,
unsafe reducibility option, or admission is added. Algorithms, construction
data fields, and security statements are unchanged.

## Downstream and verification limit

The only direct library caller found is `hashAndSign.correct`, frozen source
286. Its `rw [runAt_hsGen]` still matches the same left-hand side and input
arguments. Later local generator/index expressions at source 290 and 292 must
use the same transported tape rather than raw `rg`. This proposal intentionally
does not modify that second proof block.

The independent `runAt_hsSign` header issue (263), the signing-coin transport
needed by `S.correct` (301), and the Lamport message-length premise (366-367)
remain outside this proposal. The previous Lamport patch remains separate.

Static checks match both hunks to the frozen source and preserve the admission
and tactic-block counts. The proposal has not been elaborated. In particular,
the final simplifier sequence and the exported header's local-let presentation
need root's later native/sealed checks. No passing claim is made for this patch
or for the whole file.
