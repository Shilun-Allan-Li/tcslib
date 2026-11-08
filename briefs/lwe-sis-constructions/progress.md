# Campaign pulse

Checkpoint: five scoped gates pass 0 blockers, 0 majors, 0 minors and 3 continuing
notes each. The construction-core proof gate closes all 31 core obligations;
all 263 constants in that audited core have only standard axioms. The latest
adapter statement gate approves its 20-declaration surface. All 14 adapter proof
obligations are now filled and checked, with a separate proof audit still needed.
It does not certify the entire five-primitive campaign.

| Part | Current progress | Remaining work |
|---|---|---|
| DLWE/SIS foundations | Parameterized assumptions, actual finite-noise law, experiments, faithful encodings and parsers are defined; representation/core proofs pass their audits | Source-policy completion, honest samplers and implemented parameter schedules |
| Direct Regev symmetric encryption | Mathematical algorithms, every-seed bounded-error correctness and the concrete two-DLWE-advantage bound are proved and audited | Efficient machine/encoding implementations, uniform message bounds and existing primitive/game bridges |
| SIS collision-resistant hashing | Binary matrix hash, collision-to-SIS reduction, compression/solution existence, dyadic profile and bit budgets are proved and audited | Efficient implementation and exact raw collision-output/CRH bridge, under the independent SIS assumption |
| Regev CPA PKE | Source comparison, quantitative correctness and strong leftover-hash preflight are recorded | Formal algorithm/universality/security statement gates, proofs and machine/primitive bridge |
| PRGs | Seed-allocation, noise entropy and indexing obligations are planned | Formal construction, quantitative/efficiency proofs and existing API bridge |
| CCA2 PKE | Peikert–Waters route and supporting cryptographic trapdoors/strong one-time signature dependencies are planned | Supporting statement/proof gates and the final construction/security bridge |

The binary representation adapter module has 20 unchanged source declarations
and all 14 audited obligations proved. Its fresh 93-module check passes, all 284
owned constants use only standard axioms, and the nine public machine contracts
it consumes are axiom-clean. The next concrete gate is its separate proof audit.
The statements and their proof fill are kept separate from the audited #237 code.

## PRs and user action

GitHub currently has three open draft PRs, all targeting
`cryptography/lwe-sis-constructions`:

* [#236](https://github.com/Shilun-Allan-Li/tcslib/pull/236): representation proofs.
* [#237](https://github.com/Shilun-Allan-Li/tcslib/pull/237): direct Regev/SIS
  mathematical core, now with a passing proof audit.
* [#238](https://github.com/Shilun-Allan-Li/tcslib/pull/238): binary representation
  adapter proofs; Codex's statement audit passes, all 14 proofs are checked and
  the separate proof audit is being prepared.

The first two have passing scoped audits, but neither is marked clear to merge: source
validation/ingestion/matching and applicable landing checks remain. No merge
action is requested now. The user alone approves and merges. The adapter's exact
published exchange input is `a0b0d03b5694a0e9ab3df3ff6dfdd88ed7326ef4`;
its statement freeze remains `6eec97be8f54d9990340900a5595dab32fb477f5`.
The filled Lean/root is `b9ce3521e7f5a15d80e71bf5e9be4c48bc73010e`;
publication of this proof update is not yet claimed.
The separate proof-review packet is locally prepared and checked in 1009
sections. Codex is freshly selected; client publication and user dispatch
remain pending. See `fills/02-encoding-adapters/DISPATCH.md`.

No search/decision/worst-case lattice bridge, SIS–LWE reduction, short lattice
basis or Gaussian preimage sampling has been introduced. The exact proposed
shared probability-reader and source-registry diffs remain unapplied.

**Not yet clear to merge — scoped audits pass; source-policy work, landing checks
and user approval remain. The adapter proofs are checked; their audit is next.**
