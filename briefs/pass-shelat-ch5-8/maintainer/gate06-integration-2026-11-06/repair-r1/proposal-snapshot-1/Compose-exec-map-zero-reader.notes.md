# Compose: one zero-execution reader repair

**UNAPPLIED; native elaboration and sealing pending.** Frozen Gate06 head supplied by root:
`e9d64158461bfe24ddc88ab885bc4017899b4c16`. The library source remains unchanged.
No Lean/cache, Git command, app, or library edit was used in preparing this proposal.

The valid V3 ordinal23 seal reports three source diagnostics. All 612 requested names were
installed and verified (612 active, zero already irreducible), and EOF verified all 612.
The manifest maps them as follows:

| Probe line | Frozen source line | Existing declaration | Cause |
|---|---|---|---|
| 167 | 117 | `Compose.exec_eq_map` | Zero branch `rfl` reads foreign `exec` at zero. |
| 491 | 441 | `HybridProtocol.compose_P_coinLen` | `rfl` reads foreign `Strategy.coinLen` and `PolyExpr.eval`. |
| 495 | 445 | `HybridProtocol.compose_V_coinLen` | Same coin-length/evaluation body dependency. |

This patch changes **only the zero leaf in the existing `exec_eq_map` proof block**:
`rfl` becomes `simp only [exec_zero, List.range_zero, List.filter_nil, List.map_nil]`.
`exec_zero` is the existing public theorem at `ZeroKnowledge/Interaction.lean:256`.
The other three entries are public Core List lemmas (verified in the pinned v4.25.0
`Init/Data/List/Basic.lean` at lines 2032, 487 and 466). No foreign definition occurs
in the explicit simplifier list; the successor proof is byte-for-byte unchanged.
No new declaration, `by` block, hypothesis, algorithm change or admission is introduced.
The public header and all source outside that one line are preserved.

The two coin-length errors remain intentionally unpatched in this invocation. No missing
API is required for them: their existing owner-local declarations can keep the same headers
and replace `rfl` with term-level equality glue using the published readers:

* `Strategy.coinLen_eq` (`ZeroKnowledge/Interaction.lean:126`), on the composed strategy and
  the main/inner strategies;
* `compose_P` / `compose_V` (`Compose.lean:421/424`), then `composeP_coins` /
  `composeV_coins` (`Compose.lean:371/407`);
* `PolyExpr.eval_add` and `PolyExpr.eval_mul` (`Complexity/Randomized/PolyExpr.lean:117/120`).

An `Eq.trans` chain with `congrArg` / `congrArg₂` transports the strategy and polynomial
field equalities through evaluation, expands addition/multiplication with those public
lemmas, and converts both resulting `S.coins.eval n` operands back through
`(Strategy.coinLen_eq S n).symm`. This remains a term proof in the original owner, with
no helper definition or foreign body `rfl`. A subsequent separately authorized invocation
can author the first such term repair. No second proof block or coin-length patch is authored here.

Static validation checked one-hunk in-memory application, the frozen source fingerprint,
probe/source coordinates, unchanged headers and `by`/admission counts, and source bytes
unchanged after artifact creation. Root retains application and serial native checking;
this proposal addresses one of the three observed Compose diagnostics by inspection and
does not claim a passing repaired seal.

| Artifact | SHA-256 |
|---|---|
| Frozen `Compose.lean` | `07e83dc99bd2c98e6bdd0684ef4ad417b3d602d84b60f603e2b69f7a0c613f4a` |
| Proposed `Compose.lean` | `2a3c9791766a92de800a54fdbf90a39e2a66796577a0c29d5ff43708460439f3` |
| Proposal patch | `a8181d18dcae586ab6c2eb32c807aada29f17f40d23929a4ad3437330ea70bfa` |
| Public reader home `Interaction.lean` | `12141ce2905f6be5a7266b4e0abce797abe75c8c1d802f32b5ee6a30a0440198` |
| Completed V3 probe log | `de02f24541b057e83ef64010413c2888787f9ffb91469f120ff42ec2c3d169d5` |
| V3 seal manifest | `e0f7721d5a8b366fee1e247576741d152e9900423344bd200916fb38c93583af` |

Log: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_023_TCSlib_Cryptography_SecureComputation_Compose_HarnessV3.log`.
