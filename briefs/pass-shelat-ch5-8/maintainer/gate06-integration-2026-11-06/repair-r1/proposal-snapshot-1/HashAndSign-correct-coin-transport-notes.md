# HashAndSign: correctness caller proposal

Separate, unapplied patch:
`HashAndSign-correct-coin-transport.patch`.

Frozen source head: `e9d64158461bfe24ddc88ab885bc4017899b4c16`.
Source SHA256: `3cf353234d367d3526b2a76ecb1e45448540cb1082041771b3d8a9ccdfa719bd`.
No library edit, Lean/cache/build command, Git mutation, or worker-program
execution occurred. The stable S2 FINAL review files were not changed.

## Scope

The only existing proof block changed is `hashAndSign.correct` (frozen source
284-301). A readable proof-sketch paragraph is added to the existing
construction docstring because the explicit transport proof exceeds twenty
lines. All definition arguments, hypotheses, algorithms, construction data
fields, public security statements and admissions remain unchanged.

The proposal depends on the already saved generator and signer helper patches:

- `HashAndSign-runAt_hsGen-coin-transport.patch` supplies `hsGen_coinLen` and
  the explicit generator-tape equation.
- `HashAndSign-runAt_hsSign-coin-transport.patch` supplies the signer equation
  whose wrapper input is the published `coinsCongr` transport.

Both helpers and `HashAndSign-exists-lamport-msgLen.patch` were composed with
this change only in memory. The patch itself contains only the construction
docstring and correctness proof changes, against the original frozen bytes.

## Proof route

1. **Generator tapes.** Carry `rg` through `Fin.cast` using
   `hsGen_coinLen S H n`, obtaining a tape of length
   `S.gen.coinLen n + H.gen.coinLen n`. Its first segment is
   `rg1 : S.gen.Coins n`; its second is `ri : H.gen.Coins n`. Let the hash
   index be `i = H.gen.runAt n [] ri`. The revised `runAt_hsGen` gives the
   paired keys with this index. The local `hgen` proof is an application of
   that public equation, with only local-let conversion.
2. **Signer tapes.** Let
   `e : S.sign.Coins n` equivalent to `(hsSign S H).Coins n` be the same
   `NUPPT.coinsCongr` used by the revised helper header. Its polynomial
   equality is the symmetric `NUPPT.coins_ofPolyTimeUniform` equation.
   The actual wrapper tape is `rs`. Rewrite it as `e (e.symm rs)` using
   `Equiv.apply_symm_apply`, then apply `runAt_hsSign`. The original signer
   receives `e.symm rs`, not the wrapper-typed `rs`.
3. **Verification word.** Use `hsVerFun_eq`, `atParam_eq` and the pairing
   projection equations to expose the original verifier on the hash word and
   the original signer's output. No foreign or owner definition body is
   explicitly unfolded.
4. **Hash-message transport.** `List.length_replicate` and the unchanged
   premise `hlen n` give the equality between the padded hash width and
   `S.msgLen.eval n`. Form the typed message `mh` by the corresponding
   `Fin.cast`. `List.ofFn_congr`, `ofFn_padFin_eq_padStr` and `hsHashList_eq`
   give `List.ofFn mh = hsHashList H (List.replicate n true) i (List.ofFn m)`.
5. **Original correctness.** Apply `S.correct n mh rg1 (e.symm rs)` and
   transport its encoded message with that list equation. The result is the
   required verifier output `[true]`.

All short equalities are term proofs. The new version has one correctness
tactic block and no nested tactic blocks; the two old nested `hl`/`hm0`
blocks are replaced by terms. No global lemma/helper definition is added.
The tape equivalence is used abstractly through its type and public equations,
never by reducing `coinsCongr`. Zero-length generator segments, signing tapes
and hash messages are covered without positivity assumptions.

## Static checks and remaining limits

- Both patch hunks match the frozen source exactly.
- All three earlier patches compose with it in memory; none was applied to
  the worktree.
- The construction's non-proof fields and header are unchanged; the security
  theorem and its original admission are untouched.
- Only the existing correctness block is revised. The complete composition
  targets every root/cascade reported in the initial HashAndSign seal, but
  has not been elaborated and is not a passing claim.

Root should later check the composed file natively and under the whole-file
seal. In particular, the rewrite from the local equivalence to the explicit
helper-header transport, local-let matching in `hgen`, and the final `simpa`
remain untested API-applicability details. No further caller or proof was
edited during this invocation.
