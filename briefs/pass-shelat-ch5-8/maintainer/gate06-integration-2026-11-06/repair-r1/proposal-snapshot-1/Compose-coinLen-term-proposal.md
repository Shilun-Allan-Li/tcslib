# Compose coin lengths: two term-only public-reader proposals

**Unapplied, unchecked proposal.** Explicit source worktree:
`/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4`.
Frozen HEAD: `e9d64158461bfe24ddc88ab885bc4017899b4c16`.

Scope: replace only the existing `:= rfl` bodies of `HybridProtocol.compose_P_coinLen` and `compose_V_coinLen` by term `calc` equality chains, with short accompanying proof sketches. **Zero tactic blocks.** Their headers are literally unchanged up to `:=`; all definitions, algorithms, premises, admissions, other declarations and proof bodies are preserved.

## Valid V3 evidence and precise roots

Completed log:
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_023_TCSlib_Cryptography_SecureComputation_Compose_HarnessV3.log`.

The V3 marker records 612 requested/active/verified names, none already irreducible; the EOF verifier is present. The completed run JSON records rc 1, no fresh object and three source diagnostics.

| Selected declaration | Frozen source | V3 probe | Failing equality |
|---|---:|---:|---|
| `compose_P_coinLen` | 441:87 | 491:87 | composed Alice coin length = main Alice length + calls × run Alice length |
| `compose_V_coinLen` | 445:87 | 495:87 | composed Bob coin length = main Bob length + calls × run Bob length |

Both `rfl` proofs reduce the imported ordinary `Strategy.coinLen`. Its public owner reader already exists at `ZeroKnowledge/Interaction.lean:126`, so no Interaction/API addition is required.

The **third diagnostic is deliberately untouched**: `Compose.exec_eq_map`'s zero-case `rfl`, frozen source 117 / V3 probe 167, reads `exec … 0`. This patch does not claim to repair the complete module.

V3 log SHA-256: `de02f24541b057e83ef64010413c2888787f9ffb91469f120ff42ec2c3d169d5`.
V3 probe SHA-256: `ad825d64ffb7556eb1ce9d352746d78b5e24a473bfca38af599329bfdcddb5aa`.

## Term-proof route

Each chain performs the same four steps, with `P/composeP` for Alice and `V/composeV` for Bob:

1. Apply `Strategy.coinLen_eq` to the composed strategy, then project the existing `compose_P` or `compose_V` equality by `congrArg (fun S : Strategy => S.coins.eval n)`.
2. Read the coin polynomial through existing `composeP_coins` or `composeV_coins`, projecting the equality by `congrArg (fun p : PolyExpr => p.eval n)`.
3. Evaluate the polynomial sum and product through public `PolyExpr.eval_add` and `PolyExpr.eval_mul`.
4. Use the two component strategies' `Strategy.coinLen_eq` equations in reverse, under addition and multiplication via `congrArg₂` and `congrArg`.

The foreign `Strategy.coinLen` body is never reduced. `PolyExpr.eval` is read through its public evaluation equations. The local composition/strategy fields are read through existing owner equations even though local reduction would be legal here. The only new proofs are ordinary equality terms: no `by`, tactic list, foreign-definition unfolding, helper definition, host, simp attribute or admission is introduced.

## Existing upstream APIs for ComposePhases

No new upstream field reader is missing for these tape-length statements. Consumers should retain the existing public route:

| What a consumer needs | Existing owner interface |
|---|---|
| The composed protocol's parties | `HybridProtocol.compose_P`, `compose_V` (Compose:421,424) |
| Their next-message functions | `composeP_next`, `composeV_next` (Compose:358,395) |
| Their coin polynomials | `composeP_coins`, `composeV_coins` (Compose:371,407), after reading the party field |
| Numeric tape lengths | repaired `compose_P_coinLen`, `compose_V_coinLen`; generic `Strategy.coinLen_eq` |
| Move polynomial / its evaluation | `compose_rounds`, `compose_rounds_eval` (Compose:427,432) |
| First mover / leading filler | `compose_verifierFirst`, `lead_eq` (Compose:437,224) |

Current ComposePhases already explicitly uses `compose_P/V` and `composeP/V_next` in its main/run phases. Later consumer repairs should use these equations instead of unfolding foreign `compose` or `composeP/V`.

For its final transcript/view/output readers, the foreign protocol owner also already publishes `Protocol.transcript_eq`, `viewP_eq`, `viewV_eq`, `outP_eq`, `outV_eq` in Interaction (495,477,456,444,435). Thus the implicit `show`/term-conversion reads near ComposePhases:519,530,542,558,577 should be repaired through those interfaces in separate bounded invocations; this patch neither edits those consumers nor claims their full audit is complete.

## Fingerprints and static checks

| Item | SHA-256 |
|---|---|
| Frozen Compose source | `07e83dc99bd2c98e6bdd0684ef4ad417b3d602d84b60f603e2b69f7a0c613f4a` |
| Proposed Compose source, in memory only | `fa4e51378fd2c0a4499ace456a6619b9a2ec6dcd9433a65b7a2595d641c6bd12` |
| Unapplied patch | `d6ad8ca9633c82ed1f559975173653b90a1cd6a5a50ce9d88fb0a444ff155600` |

The original pair of declaration blocks matched once. Before/after splitting around those two blocks confirms that all other source bytes are unchanged. Both original headers were compared literally through `:=`. The new term bodies contain no `by`, and the file's `:= by` count is unchanged. HEAD and live source were checked against the frozen values.

Root must native-check both terms under the valid V3-style seal and inspect their collected reads/axioms. The residual `exec_eq_map` failure and later ComposePhases consumers remain separate work. No native pass or complete-module clearance is claimed.

No Lean/cache, apps, Git mutations or library edits occurred. Only the requested ignored proposal patch and notes were saved.

**Not yet clear to merge — the term proposals are unapplied/unchecked, and the independent exec_eq_map zero-case failure remains.**
