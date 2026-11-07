# ComposePhases: four remaining wrappers as public-reader term proofs

**UNAPPLIED; native elaboration and sealing pending.** All source and owner context is pinned
by read-only `git show e9d64158461bfe24ddc88ab885bc4017899b4c16:<path>`. No library edit, Lean/cache command, Git mutation
or app was used. Root's mutable working copy is not the proposal context.

These four separate patches replace only existing proof bodies of `compose_viewP`,
`compose_viewV`, `compose_outP` and `compose_outV`. Each removes its old `by` proof and
publishes an `Eq.trans`/`congrArg` term chain. **Zero new tactic blocks are authored.**
Public statement text before `:=`, hypotheses (including the unchanged `hM` output premise),
all algorithms/data fields and admissions are preserved.

Valid ordinal24 maps the observed sites to source530/542/558/577 (probe580/592/608/627).
All 625 names were verified at INSTALL and EOF. Each proof previously used `show` to read
a sealed foreign protocol wrapper. The existing public readers suffice:

* Views start with `Protocol.viewP_eq` / `Protocol.viewV_eq`.
* Outputs start with `Protocol.outP_eq` / `Protocol.outV_eq`.
* The symmetric `Protocol.transcript_eq_transcriptWith` connects their `transcriptWith`
  received-message pair to the honest transcript; existing `compose_transcript` supplies
  its phase decomposition.
* Views lift that equality through their `View` constructors with `congrArg`.
* Outputs lift it through the respective strategy's `next` application, then compose with
  existing `compose_P_next_main` / `compose_V_next_main` at
  `m := H.main.rounds.eval x.length`. The premise is exactly `fun _ => hM`.

No foreign ordinary definition is opened, no new owner reader or helper definition is
needed, and no public header has an inferred hole. The term annotations only expose the
pair of received-message lists already present in the contract. Constructor projections
of the resulting explicit pairs finish the structural equality.

Static validation checked each frozen-context single-hunk patch independently, exact
header preservation, reader presence and source coordinates. It then applied the previous
zero-case and transcript proposals **in memory only**, followed by all four new patches.
All 24 orders of these four disjoint patches yielded the same combined source. The new
source has four fewer `by` blocks and unchanged admission counts. Together all six original
ComposePhases diagnostics have proposed public-reader repairs; this is a source assessment,
not a checked theorem or a passing seal. Root retains application and serial native checks.

| Artifact | SHA-256 |
|---|---|
| Pinned source | `629dedd3dcead79d9792867e714252e7257ab2219a394044b7b6617143284fcc` |
| Previous zero + transcript source | `fd93c839eaa045df315dc759f9bcbdb1ff07242cb41fb6404cc12db66a979374` |
| Combined six-repair source | `2c2c462f1da2f14062044b6fc1a89187f9dd483cfeacc28e96c7ab67eead711a` |
| `viewP` patch | `33e74adfb327bd6bfb888a1d74846774bf3d2ac57ccff04382d093e8c5e43f66` |
| `viewV` patch | `7a99643dea367280a49c748c168f457b3eef383f459ba5e4a5267aedcab6d6fb` |
| `outP` patch | `99253fd81e8f49ee0ee8034812c2388043b70466882ff59487a1ba791d5dd438` |
| `outV` patch | `82a900fbfe0c203594ec1fe3a080214b97a9044a5d7699062a1e71e97cdce59f` |
| `viewP`-only proposed source | `dd1500a9154639d5ff68280cd2297c606fb74c55604d995d40774f06bf7595b2` |
| `viewV`-only proposed source | `c04e1249f9292349f68e7cf7da4a17bde824398a3ff6fb9469d3c127cf4ceec1` |
| `outP`-only proposed source | `2787dccb47207b334c874e8dfc68868561f968ec565b49721dd379b52e04565b` |
| `outV`-only proposed source | `4ec24d3fb0ece0eae7bf90ce570ccb1d3a464f9ee9b0be6f08cff50e29ad36bd` |
| Pinned `Interaction.lean` reader owner | `12141ce2905f6be5a7266b4e0abce797abe75c8c1d802f32b5ee6a30a0440198` |
| Original valid-seal log | `b4d1ab69ff032e744552059308049fa74c70806655bc1a876a7a0af4a750b759` |
| V3 manifest | `e0f7721d5a8b366fee1e247576741d152e9900423344bd200916fb38c93583af` |

Previous proposals are `ComposePhases-exec-run-zero-reader.patch` and
`ComposePhases-transcript-readers.patch`. Actual log: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_024_TCSlib_Cryptography_SecureComputation_ComposePhases_HarnessV3.log`.
