# Yao hybrid security and real-protocol round premise: distinct sealed roots

**UNAPPLIED; native elaboration and sealing pending.** All contexts are from exact commit
`e9d64158461bfe24ddc88ab885bc4017899b4c16` using read-only `git show`. No library edit, Lean/cache command, Git mutation
or app was used. Root's current working-copy changes are independent of these pinned patches.

The valid logs show **different causes**, so the patches preserve the two precise security
notions and do not mechanically apply the wrong HBC `iff` variant:

| Module | Probe/source | Actual root | Proposal |
|---|---|---|---|
| Yao (ordinal34) | 1025/975 | Tuple notation is checked against sealed `HybridProtocol.HBCSecure`. | Wrap the identical existing pair with `(HybridProtocol.hbcSecure_iff (yaoHybrid ...) (yaoFunctionality Y)).mpr`. |
| YaoReal (ordinal35) | 162/112 | Its existing round-positivity lambda uses `show` to read foreign `yaoHybrid.main` and `yaoMain.rounds`. This is **not** an HBC tuple diagnostic. | Replace only that lambda by a term transport through public main/round equations. |

`HybridProtocol.hbcSecure_iff` is the public hybrid predicate reader in `Hybrid.lean:267`.
Its clauses are hybrid polynomial time and the same two hybrid real/ideal simulator bounds.
The concrete protocol predicate's reader is `SecureComputation.hbcSecure_iff` in
`Defs.lean:184`; it concerns `HBCSecure (π : Protocol) F`. It is not needed in the YaoReal
repair: `hbcSecure_compose` already returns that concrete predicate and the unchanged original
term continues to use it directly. No hybrid/concrete security predicate is interchanged.

`Yao-hybrid-HBC-reader.patch` adds only the hybrid `iff.mpr` around the existing
`yaoHybrid_polyTime` and `yaoHybrid_simulators` terms. Their arguments, joint PRF assumption,
statements and proof dependencies are identical. Both underlying substantive proof bodies
and every admission remain unchanged.

`YaoReal-main-rounds-reader.patch` preserves the entire composition/security term except its
side-condition lambda. For each `n`, `congrArg` lifts `yaoHybrid_main` to the main protocol's
round count, lifts `yaoMain_rounds` through evaluation, and composes with
`PolyExpr.eval_const 2 n`. This gives the public equality
`(yaoHybrid ...).main.rounds.eval n = 2`; `Eq.mpr` transports `Nat.succ_pos 1` back through
its positivity predicate. No foreign definition body is read. The existing `by show ...;
simp` lambda is removed, and **zero new tactic blocks** are introduced across both proposals.
No new owner reader or helper definition is needed.

All public headers, inputs, premises, security notions/games, data algorithms and admissions
are preserved. The simulator/composition/OT theorem dependencies are unchanged; these are
mechanical interface repairs, not new proofs of the substantive admitted results.

Static validation checked both pinned manifest fingerprints/line maps and summary-bound
valid logs, independent single-hunk applications, exact unchanged surrounding bytes,
reader presence and `by`/admission counts. Applying the prior decoder/Bob-output/Alice-output
proposals in memory and then the new hybrid-HBC patch succeeds; all 24 orders of those four
independent Yao patches yield identical bytes. YaoReal has its own separate one-hunk patch.
Root retains application and serial native checking; no repaired seal is claimed.

| Artifact | SHA-256 |
|---|---|
| Pinned `Yao.lean` | `d7d42232e9b74a02c2c24db0df85daa53f2b0c3e310f6e5e1afa7620441c3310` |
| HBC-only proposed `Yao.lean` | `bdaa229864e34a8d7b6d8472791eb0fbd54e11a4d01edfa60953002eae102972` |
| Prior decoder + two-output `Yao.lean` | `6cc967eab4bd62d96cf7fd777a1bf6afd0c7435a015804137f9bafe5fbced7eb` |
| Combined four-repair `Yao.lean` | `cb484c1a31ed54b553cc56c6036a4cfeb430fe958323eaf0ff833469e36330cb` |
| Pinned `YaoReal.lean` | `cdbb403ce56a1e1a263a5d734c7cafa3d90cc39fd8fde856ce149b71a1c96f74` |
| Proposed `YaoReal.lean` | `9bcdc6fc6f30673d360306cb9876d7e1b39e9d80ab287bd7a1e841c1c67327c5` |
| New hybrid-HBC patch | `f9cf130e98ec25d524635c45e056e501506d82e22953ccb0fded4318642fd909` |
| New real-rounds patch | `9459e58f1b94042097c904f17ebe6432dee067f8ae018c8f21654b36e63fa340` |
| Pinned hybrid reader owner | `e38f497172aa47fd000d4185445d8544a7e71535f9252b44a4c951ace8618dde` |
| Pinned concrete reader owner | `b761c437034a6d808d09357d6d8a4c1a841d332e1e3d12c707d506cd8c996b51` |
| Original Yao valid-seal log | `f33d4bba691e2e9f79958fdd9d0bc8cbcfcc3593980eed489f06a2361063a8d7` |
| Original YaoReal valid-seal log | `7427645cab36776ea1cefe602481ffd278badb0890c319c3b7864d73b214ef6d` |
| Survey summary | `672085e62d50fa3e4f710de667e2a135fee52fc5e9164556a4526a6dc4a7cbfd` |
| V3 manifest | `e0f7721d5a8b366fee1e247576741d152e9900423344bd200916fb38c93583af` |

Actual logs: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_034_TCSlib_Cryptography_SecureComputation_Yao_HarnessV3.log` and `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_035_TCSlib_Cryptography_SecureComputation_YaoReal_HarnessV3.log`.
