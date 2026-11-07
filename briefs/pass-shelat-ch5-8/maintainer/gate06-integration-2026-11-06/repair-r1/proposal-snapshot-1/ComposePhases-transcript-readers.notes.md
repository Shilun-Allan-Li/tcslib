# ComposePhases: honest transcript through two public readers

**UNAPPLIED; native elaboration and sealing pending.** Context is exact frozen commit
`e9d64158461bfe24ddc88ab885bc4017899b4c16` from read-only `git show`. No library edits, Lean/cache command, Git mutation
or app was used. Root may independently change the working copy.

Valid V3 ordinal24 probe569 maps to pinned source519 in `compose_transcript`. Its existing
term proves the execution equality, while the unchanged header requires an equality about
opaque `Protocol.transcript`. The definition body previously connected these by reduction.

This proposal changes only that existing term proof. First public
`Protocol.transcript_eq_transcriptWith` (`Interaction.lean:422`) connects the honest
transcript to the transcript against the honest prover. Public
`Protocol.transcriptWith_eq` (`Interaction.lean:410`) connects it to `exec` on the same
strategies, first-mover flag, inputs, tape words and round count. The original
`H.compose_exec_rounds ...` term then proves the desired phase decomposition.
All equalities are composed with `Eq.trans`; no foreign body is read, no owner reader is
missing, and no new `by` block is introduced.

The public header, protocol/data algorithms, hypotheses and substantive admissions remain
unchanged. The other four wrapper/output sites (`compose_viewP`, `compose_viewV`,
`compose_outP`, `compose_outV`) remain untouched for separate invocations.

Static validation checked the pinned manifest fingerprint, source/probe mapping, reader
existence, one-hunk patch application, unchanged outside-proof bytes and `by`/admission
counts. In-memory composition with `ComposePhases-exec-run-zero-reader.patch` succeeds
in both orders; no library file was modified. Root retains serial native checking and
no passing repaired seal is claimed.

| Artifact | SHA-256 |
|---|---|
| Pinned source | `629dedd3dcead79d9792867e714252e7257ab2219a394044b7b6617143284fcc` |
| Transcript-only proposed source | `ca19c27f768ecd61fae0d2efd74b6fc1dc1ee2389d33c663fe42f189caf6b7b7` |
| Combined zero + transcript source | `fd93c839eaa045df315dc759f9bcbdb1ff07242cb41fb6404cc12db66a979374` |
| New transcript patch | `f86e1a9f2a52813d99cb8ad4d16330854cb9401c26d088948b150b886d55008b` |
| Earlier zero patch | `031225a7090492de66a98fbc732ae4a1f527f3aba4c6b9ff3738f1cd29cf8d12` |
| Pinned `Interaction.lean` reader owner | `12141ce2905f6be5a7266b4e0abce797abe75c8c1d802f32b5ee6a30a0440198` |
| Original valid-seal log | `b4d1ab69ff032e744552059308049fa74c70806655bc1a876a7a0af4a750b759` |
| V3 manifest | `e0f7721d5a8b366fee1e247576741d152e9900423344bd200916fb38c93583af` |

Log: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_024_TCSlib_Cryptography_SecureComputation_ComposePhases_HarnessV3.log`.
