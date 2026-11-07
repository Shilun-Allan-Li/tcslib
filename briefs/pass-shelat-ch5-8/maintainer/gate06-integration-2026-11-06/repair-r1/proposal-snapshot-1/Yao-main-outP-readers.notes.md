# Yao: Alice's two-message output, one proof block

**UNAPPLIED; native elaboration and sealing pending.** Context is exact frozen commit
`e9d64158461bfe24ddc88ab885bc4017899b4c16`, read via `git show`. No library edit, Lean/cache command, Git mutation or
app was used. Root's independent working-copy changes are unaffected.

Valid V3 ordinal34 probe644 maps to pinned source594, `yaoMain_outP`. The original `rfl`
proof reads the foreign protocol output/transcript and execution definitions. As with the
preceding Bob-output proposal, public wrapper readers leave a two-message execution to
calculate; no pinned public two-round output shortcut exists. This invocation therefore
uses the permitted **one new tactic block for this existing theorem only**.

The proof lists only published theorem readers: `Protocol.outP_eq`,
`Protocol.transcriptWith_eq`, the four `yaoMain` field readers, `PolyExpr.eval_const`,
`exec_succ`, `exec_zero`, `moverIsV_false`, `yaoAlice_next_nil`, `yaoAlice_next_cons` and
`yaoBob_next`. Alice first sends `yaoMsg`; Bob sends his `yaoBobOut`; Alice's received
history is that singleton, so `yaoAlice_next_cons` identifies her output with Bob's result.
No foreign ordinary definition occurs in the explicit simp list. Standard simplification
handles closed arithmetic, Boolean cases and List/Prod constructors. Native checking must
confirm the proposed simplifier proof.

The entire public statement before `:=`, coins/inputs, premises, algorithms and substantive
admissions remain unchanged. There is no new helper declaration, owner reader or security
assumption. Only this existing theorem's proof body changes.

Static checks verified the pinned manifest fingerprint and line map, reader presence,
unchanged outside-proof bytes/admission counts, one new `by` block and one-hunk application.
The decoder delegation and Bob-output proposals were applied **in memory only**, followed
by this patch; all six permutations of the three independent patches produced the same
combined source. Remaining hybrid-call, answer and HBC failures are deferred. No passing
output theorem or seal is claimed; root retains serial native checking.

| Artifact | SHA-256 |
|---|---|
| Pinned `Yao.lean` | `d7d42232e9b74a02c2c24db0df85daa53f2b0c3e310f6e5e1afa7620441c3310` |
| Alice-output-only proposed source | `60345ee391b06aec34b5bc54b08a56753de5beb10dfe26b8ad95e54905655f24` |
| Prior decoder + Bob-output source | `fd103050cb67b7d8b630da4d00c03740da76c86f045b5b59510196a8be5e9f4e` |
| Combined decoder + both-output source | `6cc967eab4bd62d96cf7fd777a1bf6afd0c7435a015804137f9bafe5fbced7eb` |
| New Alice-output patch | `ec31652d251edf6ec14b8192d101b29d81774e3aed83ca60e6787f594b30e04b` |
| Existing decoder proposal | `df8ad758103ae54ecaa42fdfc5c7ca889665459a1b9437372eeda47e4c18e976` |
| Existing Bob-output proposal | `5550b3908a7f23d05ee368200af11960cb4c08fec23b3ced0142434d1bfb0ac2` |
| Pinned `Interaction.lean` reader owner | `12141ce2905f6be5a7266b4e0abce797abe75c8c1d802f32b5ee6a30a0440198` |
| Original valid-seal log | `f33d4bba691e2e9f79958fdd9d0bc8cbcfcc3593980eed489f06a2361063a8d7` |
| V3 manifest | `e0f7721d5a8b366fee1e247576741d152e9900423344bd200916fb38c93583af` |

Log: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_034_TCSlib_Cryptography_SecureComputation_Yao_HarnessV3.log`.
