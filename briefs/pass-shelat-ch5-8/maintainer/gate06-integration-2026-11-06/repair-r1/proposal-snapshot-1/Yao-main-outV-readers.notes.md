# Yao: Bob's two-message output, one proof block

**UNAPPLIED; native elaboration and sealing pending.** Source context is exact frozen commit
`e9d64158461bfe24ddc88ab885bc4017899b4c16` via read-only `git show`. No library edit, Lean/cache command, Git mutation
or app was used. Root's mutable working copy is not assumed to equal this pinned context.

Valid V3 ordinal34 verifies all 1,776 requests (1,756 active, 20 already irreducible) at
INSTALL and EOF. Probe637 maps to pinned source587, `yaoMain_outV`; probe644 maps to source594,
`yaoMain_outP`. The original `rfl` proofs require foreign protocol output/transcript and
execution bodies, which are sealed. The planned decoder delegation separately retires the
private decoder length-proof failure at source375.

The output equalities require calculating a two-message execution, not only transporting a
single wrapper equality. Pinned `Interaction.lean` has public zero/successor equations for
`exec`, but no existing public two-round output theorem. This invocation uses the expressly
permitted fallback: **only `yaoMain_outV` receives one new tactic block; `yaoMain_outP`
remains untouched**. No second proof block is authored.

The single `simp` proof lists only published theorem readers:
`Protocol.outV_eq`, `Protocol.transcriptWith_eq`, the four non-simp `yaoMain` field readers,
`PolyExpr.eval_const`, `exec_succ`, `exec_zero`, `moverIsV_false`, `yaoAlice_next_nil`, and
`yaoBob_next`. They evaluate the unchanged two-round, Alice-first protocol: Alice sends its
`yaoMsg`, Bob receives that singleton history, and his output is `yaoBobOut` on that message
and his answers. No foreign ordinary definition is named in the simplifier list and no
raw machine body alias is introduced. Standard simplification handles the closed arithmetic,
Boolean branches and List/Prod constructors. Native replay must validate the tactic result.

All statement text before `:=`, inputs/coins, premises, protocol/data algorithms and
substantive admissions are unchanged. No new owner reader, helper declaration or assumption
is needed. The remaining Alice-output, hybrid-call, answer and HBC sites are deferred.

Static checks verified the pinned manifest fingerprint and coordinates, existence of the
public reader declarations/generation directive, unchanged source outside this proof and
admission counts, one added `by` block, and one-hunk application with context that uniquely
identifies Bob's theorem. In-memory composition with `Yao-decodeMsgs-delegate-decWords.patch`
succeeds in both orders; that proposal itself remains unapplied here. No passing output
theorem or seal is claimed. Root retains application and serial native checking.

| Artifact | SHA-256 |
|---|---|
| Pinned `Yao.lean` | `d7d42232e9b74a02c2c24db0df85daa53f2b0c3e310f6e5e1afa7620441c3310` |
| Bob-output-only proposed source | `3dd271a30e8539caa76434b3241ea740a1913390f38bc47b2c8faaf29c77e89f` |
| Combined decoder + Bob-output source | `fd103050cb67b7d8b630da4d00c03740da76c86f045b5b59510196a8be5e9f4e` |
| New output patch | `5550b3908a7f23d05ee368200af11960cb4c08fec23b3ced0142434d1bfb0ac2` |
| Existing decoder proposal | `df8ad758103ae54ecaa42fdfc5c7ca889665459a1b9437372eeda47e4c18e976` |
| Pinned `Interaction.lean` reader owner | `12141ce2905f6be5a7266b4e0abce797abe75c8c1d802f32b5ee6a30a0440198` |
| Original valid-seal log | `f33d4bba691e2e9f79958fdd9d0bc8cbcfcc3593980eed489f06a2361063a8d7` |
| Survey summary | `672085e62d50fa3e4f710de667e2a135fee52fc5e9164556a4526a6dc4a7cbfd` |
| V3 manifest | `e0f7721d5a8b366fee1e247576741d152e9900423344bd200916fb38c93583af` |

Actual log: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_034_TCSlib_Cryptography_SecureComputation_Yao_HarnessV3.log`.
