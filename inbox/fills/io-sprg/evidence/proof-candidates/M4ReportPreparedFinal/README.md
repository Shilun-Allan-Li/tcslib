# M4 report update packet — renderer UNRUN, M4 incomplete

This directory prepares only a temporary report update. Nothing in active evidence, source, Git, Lean, cache, final gates or child agents was changed or invoked. The staging producer was executed only to read existing source/records and write this packet. `render_m4_report.py` was parsed with Python AST only and has NOT been executed. No M4 READY report or gate pass is claimed here.

## Preserved baseline and current snapshot

`baseline/M3-REPORT.md` is the COMPLETE existing evidence/REPORT.md copied byte-for-byte. The template inserts all these bytes unchanged into a clearly marked historical appendix, including all fidelity/Rule15/target-selection/non-vacuity tables; Phase B; StatementChanges; deviations; both process breaches; complete M0–M3 historical gates; opacity/warning repairs; and source commit ledger. The current layer explicitly supersedes the appendix's former M3 publication-pending wording using captured baseline/M3-delivery.json: exchange 2a9ccadc2772789ace445490f6df8d231ff1221b, source04249b8, exact6349 paths, zero hash mismatches, successful non-force push.

`snapshot-IN_PROGRESS.json` captures root dispatch context c44841d3ba8af56a407d3d30b7c4720617c0d845, 34 observed owners, 698 headers, 93 moves, 28 inserted cumulative helpers (27 checked), 155 saved steps (154 checked; step154 pending), 127 completed originals, and19 remaining original direct holes. The source may continue changing while root works. These observations are NOT bound to a fresh final committed-source inventory or gates. Future rendering recomputes source anchors/size and saved-step statuses; the input must use the intended fresh source head and artifacts.

Exact source hashes were read from existing checkpoint HEAD_at_capture records (ed37984916cfb19a91732137e4e99e75e21fe995 and3a8f1b5e4fd568cf3273d97802abddbfd5ee7dd2) and root's supplied c44841d3ba8af56a407d3d30b7c4720617c0d845. No Git command was run by this preparation. Semantic roles are recorded, but exact commit subjects/author/committer/signing metadata were NOT invented. The READY template intentionally leaves subjects pending and requires root's final exact source ledger plus full subjects before rendering READY. Append all later M4 source commits; the last must equal final head.

## Files and proposed use

- `REPORT-M4.template.md`: complete current-status layer plus exact historical M3 insertion marker.
- `declaration-plan.json`, names-M4-originals.txt, names-M4-helpers.txt: fixed16 originals and proposed13 helpers, with current snapshot anchors/statuses; no helper renamed or silently added.
- `input.schema.json`: dynamic input contract. `input-READY.TEMPLATE.json` deliberately contains invalid PENDING paths/hashes/head and cannot claim READY as supplied.
- `render_m4_report.py`: root-review candidate. It reads bound artifacts/current files and writes a NEW directory under /private/tmp only. It has no subprocess, Git, Lean or cache invocation. It refuses an existing output path and never writes evidence/REPORT.md.
- `overlap-admission.TEMPLATE.json`: exact29-name provenance format, all reviewed=false/PENDING. This template is NOT an admission record or search result.

Proposed root invocation after review (NOT executed here):

    python3 -I /private/tmp/io-sprg-proof-notes/M4ReportPrepared/render_m4_report.py \
      --input /private/tmp/io-sprg-proof-notes/M4ReportPrepared/snapshot-IN_PROGRESS.json \
      --out /private/tmp/io-sprg-proof-notes/M4ReportDraft-fresh

For final M4 readiness copy input-READY.TEMPLATE.json to a fresh input, replace ALL placeholders with actual fresh artifacts and final source hash, append exact source commits/subjects, and run to a fresh temporary directory. The input JSON must remain beside the baseline/template/declaration files, or copy that small packet together. This is an untested formatting/cross-checking adapter, not a replacement for root's required source/freeze/build/overlap/gate audit.

## Artifact contract

Every fresh_gates artifact is either null (IN_PROGRESS only) or `{path,sha256}` for an existing file. Relative paths resolve against the managed worktree. SHA256 binds the exact supplied artifact. `selected_probe` and `headline_probe` are exact probe module strings, not files. Gate artifacts:

- committed_inventory: V2-style committed inventory (`head`, pinned`base`, `mode=COMMITTED_HEAD`, exact`owners`, `owner_sources`, `source_sha256`). The renderer checks all captured source bytes and complete current owner filesystem coverage; root separately establishes committed-diff/ancestry authority.
- source_inventory: current head/source hashes, named_sorry_bodies, remaining_named_obligations. READY requires exactly the frozen M5seven+M6nine names, not merely a count16.
- all_owner_build: results.jsonl FILE from the fresh full build. Adjacent mods/ logs are hash-checked; every owner must have rc/errors/error_forms0, exact source/head/log/current object hash in environment_tree. No old prefix build or successful partial queue counts as full coverage.
- static_summary: current head/owner count, checks dict, all_widths_pass, new_campaign_fail_warn. Every check other than historical campaign rc must be0 and there must be no new campaign findings. These are supplied root checks, not invoked by the renderer.
- freeze_summary: full current global source freeze. Requires all670 unchanged, zero removals/header/prose changes, exact source hash coverage and actual move ledger. WORKTREE_CANDIDATE label remains honestly separate from committed/full-kernel evidence.
- selected_axiom_summary: same M3-style `head`, `probes` object keyed by exact module, each with `axioms:{FQN:[axioms]}`. selected_names and headline_names are JSON string arrays; selected_owner_names is a unique JSON array of exact dotted owner modules. Selected/headline sets must match their exact lists, duplicated prints must agree, and allM4 originals/helpers plus cumulative helpers must be standard-only in their union. Later headlines may still have only declared sorryAx in addition to standard axioms.
- warning_summary: head, expected_remaining_sorry_warnings, other_warnings; expected sorry count must equal source holes and other_warnings must be empty.
- slot_summary: fresh root slot_history_v2 JSON with exact historic93883/93983 timestamps, historical serial=false/max2, verified post-correction serial=true and active0. Adjacent slots-io-sprg.log and current tagged source lines must match its extracted hash; no later tagged event may be hidden. Full process/cap claims stay excluded.
- commits_ledger: exact final source commit ledger file; every listed M4 hash must occur. Root supplies exact subjects in source_commits and retains all patch/author/committer/signing authority in the real ledger/package.
- overlap_summary: root-reviewed29-row artifact matching overlap-admission.TEMPLATE.json, with actual name/shape and exact/apply source/log hashes and scopes. Invalid public-binder/V1 or harness failures remain retained but cannot substitute for fresh admitted pairs. Actual-reader scopes must affirm target absence from bound imports; public-only mathematical cores exclude owned imports. The renderer hashes provenance artifacts; it does not perform searches or infer global absence.

IN_PROGRESS accepts null gates and prints explicit PENDING rows. READY requires all fresh inputs, all16 original and13 helper saved CHECKED_PASS records, no pending step, exact16 later original holes, complete owner/current-source/object/build coverage, all required standard-only print identities and search-admission rows. It still says M4 packaging/publication pending and final canonical gates/PhaseB unfinished. Fresh full stored-root graph, full generated kernel types, all four Rule10 variants and controls remain final later gates; the tool does not claim them based on selected prints.

## Proof/provenance organization

M4 originals are six hybrid statements, six encoding statements, PRGhop, LPNhop, lemma42, prop41. Four PRG helpers are sdCore_publicSeed (Hybrids, early to avoid cycle), prg_verdict_prob, prg_nuisance_average and prg_chain_accept_average. The latter three are PRG/Hop. The PRG narrative records mandatory most-specific RealizesOn reuse, pure prefix marginalization, actual nuisance law, explicit advice-product transport and the public inverse-constructor reader; discarded repairs are not additional checked proofs.

Nine LPN helpers are verdict, gap, uniform challenge reindex, real joint draw reindex, real/uniform preprocessing, real/uniform sections, and advice averaging. At the dispatch helper04/step154 was inserted but unchecked; helper05–09 and lpn_hop were pending. They remain explicit placeholders until fresh saved checks and search records exist. The source inspection can see a newly inserted helper before its step record; this is labelled PENDING_NO_CHECKED_STEP_BOUND, not a proof pass.

The PRG sdCore binder `public` pair was invalid and is superseded by root's `publicMap`v2. Name/shape logs are at evidence/overlap/M4-PRG-name-shape and M4-LPN-name-shape; helper specs/placement and source/probe hashes are under proof-candidates. Actual earlier-owned-definition probes are separate from public-only expanded cores. OwnM0 constants and newly installed helper targets cannot be allowed to self-match. Exact frozen all-realisers/all-κ and advice-family quantifiers, rationalδ, canonical assumption encodings, T6 witness uniformity before schedules and PhaseB obligations remain unchanged.

## Limits

No READY renderer/gate/package invocation occurred. No report says M4 complete in this packet. No current full canonical matrix/census is inferred from historicalM0 or selectedM3/M4 print scopes. The whole M3 report is retained literally, rather than editing historical counts/anchors into apparent current evidence. The external report-binding.json will contain the generated report hash to avoid circular self-hashing. Root remains responsible for exact package replay, bundles, all-tree PDF exclusion, manifests and later successful non-force publication record.
