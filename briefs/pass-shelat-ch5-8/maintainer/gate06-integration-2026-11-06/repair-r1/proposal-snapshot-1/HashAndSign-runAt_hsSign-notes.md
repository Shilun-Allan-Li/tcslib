# HashAndSign: explicit signer-coin transport

Separate, unapplied proposal against frozen head
`e9d64158461bfe24ddc88ab885bc4017899b4c16` and source SHA256
`3cf353234d367d3526b2a76ecb1e45448540cb1082041771b3d8a9ccdfa719bd`.
No library source was edited and no Lean/cache/Git command was run.

Patch: `HashAndSign-runAt_hsSign-coin-transport.patch`.
The existing generator proposal was composed with this change only in memory;
neither patch was applied to the worktree. The Lamport-corollary patch is not
part of this proposal.

## The one repaired helper

Only the header presentation and existing tactic block of `runAt_hsSign`
(frozen source 261-267) change. All original arguments remain, including
`r : S.sign.Coins n`. There is no new hypothesis or restricted input.

The original header's bare use of `r` as the wrapper's tape is ill typed under
the foreign-definition seal. The revised header carries it explicitly through
`NUPPT.coinsCongr`, with both endpoint machines supplied:

- source machine `A := S.sign`;
- destination machine `B := hsSign S H`;
- coin-polynomial equality: the symmetric public
  `NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_hsSignFun S H) S.sign.coins`.

Thus the wrapper receives a tape of precisely `(hsSign S H).Coins n`; the
right-hand side retains the original tape `r`. The same-file `hsSign`
abbreviation is notation. The foreign constructor and `coinLen` bodies are
never read through reduction.

No new owner-side reader is needed for this small repair. Existing public APIs
already supply the exact types and equations:

- `Randomized/PPT.lean:241`: `coinsCongr h n : A.Coins n` equivalent to
  `B.Coins n` when `h : A.coins = B.coins`.
- `PPT.lean:245`: `coinsCongr_ofFn h n r` states that this equivalence preserves
  `List.ofFn r`.
- `PPT.lean:251`: `runAt_coinsCongr h n y r` reads the transported typed run as
  `B.runAtL n y (List.ofFn r)`.
- `PPT.lean:393`: `coins_ofPolyTimeUniform` publishes the wrapper's coin
  polynomial.

The single tactic block uses `runAt_coinsCongr`, the wrapper's public
`runAtL_ofPolyTimeUniform`, and the original signer's `Uniform.runAt_eq`.
It then simplifies the raw layout through owner reader `hsSignFun_eq` and the
published input/layout/pairing equations. `coinsCongr` is used as an abstract,
typed term; it is not named in an unfold, rewrite, or simplification list.

The equivalence is bijective and preserves the whole coin list, so it covers
all wrapper tapes and preserves the same signing equation. Zero-length signing
tapes are included. No algorithm, construction data field, security statement,
admission, helper definition, or attribute changes.

## Caller intentionally left for the next invocation

The only direct library caller is `hashAndSign.correct`, frozen source 288.
It currently has `rs : (hsSign S H).Coins n`, whereas the helper's input remains
an original-signer tape. Its later repair should carry `rs` back through the
inverse of the same equivalence, use the helper on that tape, and use the
public `Equiv.apply_symm_apply` equation to recover the wrapper tape. The
original signer tape can then be passed to `S.correct` at source 301.

The generator/index transports from the separate `runAt_hsGen` proposal are
also still needed in that correctness block. Neither this caller nor any
second tactic block is changed here.

## Verification limit

The patch matches the frozen bytes, and an in-memory composition with the
saved generator patch preserves the entire scheme/security suffix verbatim.
No new admission or tactic block is added. The native and sealed elaborations
remain unrun; in particular, root must check the header's explicit equivalence
application and the final reader simplification later. No full-file passing
claim is made.
