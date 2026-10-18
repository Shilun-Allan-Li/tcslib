# The campaign records

Process records of the formalization campaign (Arora–Barak chapters 1–4 and 7): audit gates, fill
rounds, design notes and logs. The library itself is `TCSlib/`; the standards are `policy.md` and
`workflow.md` at the repository root. Restructured on 2026-10-18 from the flat `audits/` and
`briefs/` folders; `MOVED.md` maps every old path to its new one.

## Layout

| Folder | Contents |
|---|---|
| `standards/` | the audit template (`TEMPLATE.md`) and the fill-environment addendum |
| `gates/<NN>-<slug>/` | one folder per audit gate: `pack.md`, `findings.md`, `resolutions.md`, later rounds as `pack-r2.md`, `findings-r2.md`, the bundle list, `evidence/` and `logs/`. `NN` is the dispatch number where the gate had one (gates from folder 1 on) |
| `fills/<group>/` | one folder per fill workstream: `briefs/`, `orders/` (bootstrap order lists), `inputs/<brief>/` (probes, overlays, screen populations), `drafts/`, `reports/` (the workers' reports), `reviews/`, `logs/`, `evidence/`, `integration/` |
| `items/<workstream>/` | workstream-level design notes and evidence (for example `items/c1/C1-design.md`) |
| `design/` | the chapter plans and design proposals |
| `logs/` | logs not tied to one gate or fill |
| `programs/` | the axiom-check programs |
| `backlog.md` | the running backlog |

## Gates

| Folder | Files |
|---|---|
| `gates/01-wave1-fill/` | findings.md, logs, pack.md, resolutions.md |
| `gates/02-ch34-b3a-fill/` | findings.md, pack.md, resolutions.md |
| `gates/03-ch34-b5b-fill/` | findings-r2.md, findings.md, pack-r2.md, pack.md, resolutions.md |
| `gates/04-mig0a/` | findings-r2.md, findings.md, logs, pack-r2.md, pack.md, resolutions.md |
| `gates/05-b6-restatement/` | evidence, findings.md, logs, pack.md, resolutions.md |
| `gates/10-stage2-statements/` | findings.md, logs, pack.md, resolutions.md |
| `gates/11-rd2-statements/` | findings.md, logs, pack.md, resolutions.md |
| `gates/12-c1-hosts-statements/` | findings.md, logs, pack.md, resolutions.md |
| `gates/13-b6-hosts-statements/` | findings.md, logs, pack.md, resolutions.md |
| `gates/14-h2-promotion/` | findings-r2.md, findings.md, pack-r2.md, pack.md, resolutions-r2.md, resolutions.md |
| `gates/15-mig0b/` | evidence, findings-r2.md, findings.md, logs, pack-r2.md, pack.md, resolutions-r2.md, resolutions.md |
| `gates/16-mig1-statements/` | findings-r2.md, findings.md, logs, pack-r2.md, pack.md, resolutions-r2.md |
| `gates/18-arm-extensions-fill/` | findings-r2.md, findings-r3.md, findings.md, pack-r2.md, pack-r3.md, pack.md, resolutions-r2.md, resolutions-r3.md |
| `gates/19-c1-assembly-statements/` | findings-r2.md, findings.md, logs, pack-r2.md, pack.md, resolutions.md |
| `gates/20-h1-harvest-statements/` | findings.md, logs, pack.md, resolutions.md |
| `gates/22-s13d-g24-statements/` | findings.md, logs, pack.md, resolutions.md |
| `gates/24-diagonal-p1-statements/` | findings.md, pack.md, resolutions.md |
| `gates/26-u2-statements/` | findings.md, pack.md, resolutions.md |
| `gates/27-s13d-g2-fill/` | findings.md, pack.md, resolutions.md |
| `gates/28-s13d-walk-statements/` | findings.md, pack.md, resolutions.md |
| `gates/29-spec-api/` | evidence, findings-r2.md, findings.md, pack-r2.md, pack.md, resolutions.md |
| `gates/30-core-api/` | evidence, findings-r2.md, findings.md, pack-r2.md, pack.md, resolutions.md |
| `gates/33-mig11a/` | evidence |
| `gates/34-brief-api/` | evidence, findings-r2.md, findings-r3.md, findings.md, pack-r2.md, pack-r3.md, pack.md, resolutions.md |
| `gates/37-nd-api/` | evidence, findings-r2.md, findings.md, pack-r2.md, pack.md, resolutions.md |
| `gates/38-nd-normalform/` | evidence, findings.md, pack.md, resolutions.md |
| `gates/39-ntime-diag-statements/` | findings-r2.md, findings.md, pack-r2.md, pack.md, resolutions.md |
| `gates/42-c1-writer-fill/` | findings.md, pack.md, resolutions.md |
| `gates/43-seam-layout-statements/` | findings.md, pack-r2.md, pack.md, resolutions.md |
| `gates/44-s13d-g4-cont1-fill/` | evidence, findings.md, pack.md, resolutions.md |
| `gates/45-ntime-diag-bf-statements/` | findings.md, pack.md, resolutions.md |
| `gates/12.2c-t1-blockloop/` | findings.md, logs, pack.md, resolutions.md |
| `gates/12.2c-t1-codeformat/` | findings.md, logs, pack.md, resolutions.md |
| `gates/12.2c-t1-loop/` | findings.md, logs, pack.md, resolutions.md |
| `gates/12.2c-t2a/` | evidence, findings.md, logs, pack.md, resolutions.md |
| `gates/b1-fill/` | findings.md, logs, pack.md, resolutions.md |
| `gates/b2b-fill/` | findings.md, logs, pack.md, resolutions.md |
| `gates/b7-fill/` | findings.md, logs, pack.md, resolutions.md |
| `gates/b7-statements/` | findings.md, logs, pack.md, resolutions.md |
| `gates/b8-fill/` | findings.md, logs, pack.md, resolutions.md |
| `gates/ch1-infra/` | bundle-r2.md, bundle-r3.md, bundle.md, evidence, findings-r2.md, findings-r3.md, findings.md, logs, pack-r2.md, pack-r3.md, pack.md, resolutions.md |
| `gates/ch1-libfill/` | bundle.md, findings.md, logs, pack.md, resolutions.md |
| `gates/ch2-closure/` | pack.md |
| `gates/ch2-epoch1/` | bundle.md, findings.md, pack.md, resolutions.md |
| `gates/ch2-epoch2/` | bundle.md, evidence, findings.md, logs, pack.md, resolutions.md |
| `gates/ch2-epoch34/` | bundle-r2.md, bundle-r3.md, bundle.md, evidence, findings-r2.md, findings-r3.md, findings.md, logs, pack-r2.md, pack-r3.md, pack.md, resolutions.md |
| `gates/ch2-phase1/` | bundle.md, findings.md, pack.md, resolutions.md |
| `gates/ch2-phase1-reaudit/` | bundle.md, findings.md, pack.md |
| `gates/ch2-phase1-round3/` | bundle.md, findings.md, pack.md |
| `gates/ch2-phase2/` | bundle.md, findings.md, pack.md, resolutions.md |
| `gates/ch2-phase3/` | bundle.md, findings.md, pack.md, resolutions.md |
| `gates/ch2-phase3-reaudit/` | bundle.md, findings.md, pack.md |
| `gates/ch2-phase4/` | bundle.md, findings.md, pack.md, resolutions.md |
| `gates/ch2-phase4-reaudit/` | bundle.md, findings.md, pack.md |
| `gates/ch3-p31/` | findings.md, logs, pack.md, resolutions.md |
| `gates/ch3-p32/` | findings-r2.md, findings.md, logs, pack-r2.md, pack.md, resolutions.md |
| `gates/ch3-p33/` | findings-r2.md, findings.md, logs, pack-r2.md, pack.md, resolutions.md |
| `gates/ch34-c1-fill/` | findings.md, pack.md, resolutions.md |
| `gates/ch34-p0/` | findings-r2.md, findings.md, logs, pack-r2.md, pack.md, resolutions.md |
| `gates/ch4-p41/` | findings.md, logs, pack.md, resolutions.md |
| `gates/ch4-p42/` | findings.md, logs, pack.md, resolutions.md |
| `gates/ch4-p43/` | findings-r2.md, findings-r3.md, findings.md, logs, pack-r2.md, pack-r3.md, pack.md, resolutions.md |
| `gates/ch4-p44/` | findings.md, logs, pack.md, resolutions-addendum.md, resolutions.md |
| `gates/ch6-circuits/` | bundle.md, findings.md, pack.md, resolutions.md |
| `gates/ch6-circuits-reaudit/` | bundle.md, findings.md, pack.md |
| `gates/ch6-circuits-round3/` | bundle.md, findings.md, pack.md |
| `gates/ch7-fill/` | findings-r2.md, findings.md, logs, pack-r2.md, pack.md, resolutions.md |
| `gates/ch7-phase1/` | findings.md, pack.md, resolutions.md |
| `gates/emitter-fill/` | bundle.md, evidence, findings.md, pack.md, resolutions.md |
| `gates/emitter-infra/` | bundle-r2.md, bundle-r3.md, bundle.md, evidence, findings-r2.md, findings-r3.md, findings.md, pack-r2.md, pack-r3.md, pack.md, resolutions.md |
| `gates/epoch1/` | bundle.md, findings.md, pack.md, resolutions.md |
| `gates/epoch2/` | bundle.md, findings.md, pack.md, resolutions.md |
| `gates/epoch3/` | bundle.md, findings.md, pack.md, resolutions.md |
| `gates/epoch4/` | bundle.md, findings.md, pack.md, resolutions.md |
| `gates/mig11a-statements/` | findings.md, pack.md, resolutions.md |
| `gates/nomenclature/` | findings.md |
| `gates/phase1/` | bundle.md, findings.md, pack.md, resolutions.md |
| `gates/phase1-reaudit/` | bundle.md, findings.md, pack.md |
| `gates/phase2/` | bundle.md, findings.md, pack.md, resolutions.md |
| `gates/phase2-reaudit/` | bundle.md, findings.md, pack.md |
| `gates/phase3/` | bundle.md, findings.md, pack.md, resolutions.md |
| `gates/phase3-reaudit/` | bundle.md, findings.md, pack.md |
| `gates/phase4/` | bundle.md, findings.md, pack.md, resolutions.md |
| `gates/programs-vendor/` | evidence, findings.md, logs, pack.md, resolutions.md |
| `gates/retrofit/` | evidence, findings-r1.md, pack-r1.md, resolutions-r1.md |
| `gates/retrofit-r1/` | findings-r2.md, findings-r3.md, findings-r4.md, findings-r5.md, findings-r6.md, findings-r7.md, findings-r8.md, pack-r2.md, pack-r3.md, pack-r4.md, pack-r5.md, pack-r6.md, pack-r7.md, pack-r8.md |
| `gates/routine-f1/` | findings.md, logs, pack.md, resolutions.md |
| `gates/routine-f2/` | findings.md, logs, pack.md, resolutions.md |
| `gates/routine-infra/` | findings-r2.md, findings-r3.md, findings.md, logs, pack-r2.md, pack-r3.md, pack.md, resolutions.md |
| `gates/s12-8-fill-AC/` | findings.md, logs, pack.md, resolutions.md |
| `gates/s12-8-fill-D/` | findings-r2.md, findings.md, logs, pack-r2.md, pack.md, resolutions.md |
| `gates/s12-8-statements/` | findings-r2.md, findings.md, logs, pack-r2.md, pack.md, resolutions.md |
| `gates/s12-counter/` | evidence, findings.md, pack.md, resolutions.md |
| `gates/s12-counter-fill/` | findings.md, pack.md |
| `gates/s12-framed/` | evidence, findings.md, pack.md, resolutions.md |
| `gates/s12-framed-fill/` | findings.md, pack.md |
| `gates/s13d-g1/` | findings.md, logs, pack.md, resolutions.md |
| `gates/vhost-f1/` | findings.md, pack.md, resolutions.md |
| `gates/vhost-infra/` | findings.md, pack.md, resolutions.md |
| `gates/wave1-statements/` | evidence, findings-r2.md, findings.md, logs, pack-r2.md, pack.md, resolutions.md |
| `gates/zone-infra/` | findings-r2.md, findings-r3.md, findings.md, pack-r2.md, pack-r3.md, pack.md, resolutions.md |

## Fill workstreams

| Folder | Contents |
|---|---|
| `fills/12.2c/` | reports (3) |
| `fills/12.2c-t1/` | evidence (3) |
| `fills/12.2c-t1-blockloop/` | integration (1) |
| `fills/12.2c-t1-codeformat/` | integration (1) |
| `fills/12.2c-t1-loop/` | integration (1) |
| `fills/_drafts/` | (top) (1), s13d-g4-cont1 (1) |
| `fills/_issue/` | issue-inputs (61), issue-tools (31) |
| `fills/arm/` | evidence (182), logs (39) |
| `fills/b1/` | evidence (2), integration (1) |
| `fills/b2b/` | integration (3), reports (3) |
| `fills/b4a/` | briefs (1), logs (6), orders (1), reports (1) |
| `fills/b5a/` | briefs (13), drafts (1), evidence (33), logs (39), orders (9), reports (11) |
| `fills/b6/` | briefs (6), drafts (2), evidence (1), inputs (55), logs (22), orders (6), reports (4) |
| `fills/b7/` | integration (3), logs (2), reports (5) |
| `fills/c1/` | briefs (6), drafts (35), inputs (18), logs (18), orders (6), reports (6), reviews (30) |
| `fills/ch1-lib/` | reports (10) |
| `fills/ch2/` | briefs (27) |
| `fills/ch2-epoch1/` | reports (4) |
| `fills/ch2-epoch2/` | reports (10) |
| `fills/ch2-epoch3/` | reports (8) |
| `fills/ch2-epoch4/` | reports (6) |
| `fills/ch3-p32/` | evidence (1) |
| `fills/ch3-p33/` | evidence (1) |
| `fills/ch34/` | briefs (21), logs (21), orders (17), reports (4) |
| `fills/ch34-b3a/` | inputs (13) |
| `fills/ch34-b5b/` | inputs (11) |
| `fills/ch34-c1/` | integration (1), reports (5) |
| `fills/ch4-p43/` | evidence (2) |
| `fills/ch7/` | briefs (1) |
| `fills/d7/` | evidence (2) |
| `fills/emitter/` | briefs (4), reports (4) |
| `fills/epoch1/` | briefs (4), reports (4) |
| `fills/epoch2/` | briefs (3), reports (3) |
| `fills/epoch3/` | briefs (4), reports (7) |
| `fills/epoch4/` | briefs (1), reports (1) |
| `fills/fills-4/` | integration (1) |
| `fills/fills-5/` | integration (1) |
| `fills/fills-6/` | integration (1) |
| `fills/fills-7/` | integration (1) |
| `fills/fills-8/` | integration (1) |
| `fills/h2f/` | briefs (1), evidence (6), logs (3), orders (1) |
| `fills/k1/` | logs (6) |
| `fills/lib/` | briefs (7) |
| `fills/mig12/` | briefs (1), drafts (26), evidence (12), logs (3), orders (1) |
| `fills/ndcodes/` | briefs (1), logs (5), orders (1), reports (1) |
| `fills/retrofit/` | briefs (5), evidence (4), logs (12) |
| `fills/retrofit-r1/` | reports (3) |
| `fills/retrofit-r2/` | reports (2) |
| `fills/routine-f1/` | briefs (3), evidence (3), reports (5) |
| `fills/routine-f2/` | briefs (2), evidence (2) |
| `fills/routine-infra/` | evidence (2) |
| `fills/s12/` | briefs (2), inputs (5), logs (11) |
| `fills/s12-8/` | integration (5), logs (43), reports (7) |
| `fills/s12-counter/` | evidence (1), reports (1) |
| `fills/s12-framed/` | evidence (1), reports (1) |
| `fills/s128/` | briefs (7), logs (11), orders (6) |
| `fills/s13d/` | briefs (3), drafts (1), logs (6), orders (2), reports (2) |
| `fills/s13d-g1/` | evidence (1) |
| `fills/s13d-g4/` | evidence (14) |
| `fills/u2s/` | briefs (1), drafts (1), evidence (3), logs (3), orders (1) |
| `fills/u2s-startup/` | evidence (4) |
| `fills/vhost/` | briefs (1), logs (3), reports (1) |
| `fills/vhost-f1/` | evidence (1) |
| `fills/w1/` | briefs (7), inputs (9), logs (18), orders (6) |
| `fills/w1-inputlength/` | logs (2) |
| `fills/w1-recordtable/` | logs (7) |
| `fills/w2/` | briefs (4) |
| `fills/w2-certshell/` | logs (2) |
| `fills/w2-oraclesim/` | logs (6) |
| `fills/wave1/` | inputs (16), reports (11) |
| `fills/zone/` | reports (9) |
| `fills/zone-f1/` | briefs (8), evidence (7) |

## Workstreams

`items/b2b/`, `items/b4a/`, `items/b5a/`, `items/b6hosts/`, `items/b7/`, `items/b8/`, `items/c1/`, `items/ch34/`, `items/ch34-c1/`, `items/ch34-d4/`, `items/ch34-s1/`, `items/ch34-t1/`, `items/ch34-wave5/`, `items/ch7/`, `items/diagonal-p1/`, `items/fills-4/`, `items/fills-5/`, `items/fills-6/`, `items/fills-7/`, `items/fills-8/`, `items/h1harv/`, `items/h2/`, `items/k1/`, `items/mig0/`, `items/mig1/`, `items/mig12/`, `items/mig24/`, `items/ndcodes/`, `items/rd2/`, `items/rd2-gate/`, `items/retrofit/`, `items/s12-8/`, `items/s13d/`, `items/screenfix/`, `items/stage2/`, `items/stage2-gate/`, `items/u2/`, `items/zone-f1-A2/`
