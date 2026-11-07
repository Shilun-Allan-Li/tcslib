# ComposePhases: six-site diagnosis and one zero-execution leaf repair

**UNAPPLIED; native elaboration and sealing pending.** Exact source and owner context came
from read-only `git show e9d64158461bfe24ddc88ab885bc4017899b4c16:<path>`. No library edits, Lean/cache, Git mutations or
apps were used. Root's working-copy changes are independent of these pinned contexts.

The completed survey summary binds valid ordinal24 to its actual attempt log. INSTALL and
EOF verify all 625 names (625 active, zero already irreducible). Its six diagnostics share
a common source cause: foreign ordinary definitions are used through definitional equality
in `rfl`, term assignment or `show`, while the seal requires published readers.

| Probe | Source | Existing declaration | Reader route (only the first is patched here) |
|---|---|---|---|
| 295 | 245 | `compose_exec_run` | Normalize `2*0` via `Nat.mul_zero`; public `exec_zero`; `List.range_zero` and `List.map_nil`. |
| 569 | 519 | `compose_transcript` | Term-compose `Protocol.transcript_eq_transcriptWith`, then `Protocol.transcriptWith_eq`, then existing `compose_exec_rounds`. |
| 580 | 530 | `compose_viewP` | Replace foreign-body `show` by public `Protocol.viewP_eq`; move `transcriptWith π.P` to `transcript` using the symmetric `Protocol.transcript_eq_transcriptWith`, then `compose_transcript`. |
| 592 | 542 | `compose_viewV` | Same route through `Protocol.viewV_eq` and the transcript readers. |
| 608 | 558 | `compose_outP` | Replace foreign-body `show` by `Protocol.outP_eq` and `Protocol.transcriptWith_eq`, then keep `compose_exec_rounds` and `compose_P_next_main`. |
| 627 | 577 | `compose_outV` | Same through `Protocol.outV_eq` and `Protocol.transcriptWith_eq`, then keep `compose_exec_rounds` and `compose_V_next_main`. |

All needed APIs already exist in pinned `ZeroKnowledge/Interaction.lean`:
`exec_zero` at256, `Protocol.transcriptWith_eq` at410,
`Protocol.transcript_eq_transcriptWith` at422, `Protocol.outV_eq` at435,
`Protocol.outP_eq` at444, `Protocol.viewV_eq` at456 and `Protocol.viewP_eq` at477.
No new owner reader, changed protocol field or stronger premise is needed for the observed
sites. Existing Compose data-field/strategy readers are already used later in the proofs;
root owns the prerequisite Compose zero/coin-length repairs. The six observed sites are
independent proof-conversion failures; patching the first does not repair the other five.

This proposal changes **only the zero leaf of the existing `compose_exec_run` proof block**,
from `rfl` to `simp only [Nat.mul_zero, exec_zero, List.range_zero, List.map_nil]`.
The execution theorem applies to the unchanged opaque composed strategies and first-mover
flag; no composition definition is unfolded. Every explicit simplifier entry is a theorem.
The entire successor case, public header, algorithms, hypotheses and admissions are
byte-for-byte unchanged. No new `by` block, helper declaration or admission is introduced.

Static checks validated the pinned manifest fingerprint, summary/log binding and all six
line mappings, verified seal markers, existence of every listed owner reader, single-hunk
application in memory, unchanged outside-block bytes and `by`/admission counts. The remaining
five sites await separate invocations; root retains application and serial native checking.
No passing repaired seal is claimed.

| Artifact | SHA-256 |
|---|---|
| Pinned `ComposePhases.lean` | `629dedd3dcead79d9792867e714252e7257ab2219a394044b7b6617143284fcc` |
| Proposed `ComposePhases.lean` | `d804d6ccb54945a0145555a67e9e11fa40b51805a567d98bb8a7c7b22e179e98` |
| Proposal patch | `031225a7090492de66a98fbc732ae4a1f527f3aba4c6b9ff3738f1cd29cf8d12` |
| Pinned `Interaction.lean` reader owner | `12141ce2905f6be5a7266b4e0abce797abe75c8c1d802f32b5ee6a30a0440198` |
| Actual valid-seal attempt log | `b4d1ab69ff032e744552059308049fa74c70806655bc1a876a7a0af4a750b759` |
| Survey summary | `672085e62d50fa3e4f710de667e2a135fee52fc5e9164556a4526a6dc4a7cbfd` |
| V3 manifest | `e0f7721d5a8b366fee1e247576741d152e9900423344bd200916fb38c93583af` |

Actual log: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_024_TCSlib_Cryptography_SecureComputation_ComposePhases_HarnessV3.log`.
