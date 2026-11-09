from pathlib import Path
import json,re,hashlib,collections
O=Path('/private/tmp/ab34-ro1-integration');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4')
freeze=json.loads((O/'declaration-freeze.json').read_text());native=json.loads((O/'final-native-owner-verification.json').read_text());mine={(r['path'],r['lexical_name']) for r in freeze['changed_proof_roots']}
overlap=[]
for folder,filename,group in [('/private/tmp/ab34-overnight-sg1-harvest','mechanical-chunk-mappings.json','FH3 / CH7 original five facts'),('/private/tmp/ab34-overnight-sg1-extras','chunk-mappings.json','CH7 SafeRun3 / Hardness head-tail2')]:
 for r in json.loads((Path(folder)/filename).read_text()):
  overlap.append({'family_draft':group,'path':r['path'],'declaration':r['name'],'same_owner_touched_by_RO1':any(p==r['path'] for p,n in mine),'same_declaration_touched_by_RO1':(r['path'],r['name']) in mine,'source':'previous frozen proposal, not a claim of merge/publication','required_adoption_action':'Keep that family draft whole proof when rebasing; reapply only any remaining RO1 reader need. Root owns joint native/replay checks.'})
overlap.extend([{'family_draft':'FE #241','owners':['TCSlib/Complexity/CookLevin/Hardness.lean','TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean'],'status_from_parent':'draft/pending audit; not assumed merged','scope':'RO1 one-step reader bodies only; FE-LIVE first-live prefix roots are separate. Full pending-PR pins/chunks were not supplied in this task, so exact remote-PR declaration disjointness is not asserted.'},{'family_draft':'CH7 UniversalK hinit / CodeSimulator Nat.bit reader','owners':['TCSlib/Complexity/TuringMachine/UniversalK.lean','TCSlib/Complexity/TuringMachine/CodeSimulator.lean'],'RO1_changed_roots':[r['name'] for r in freeze['changed_proof_roots'] if r['path'].endswith(('/UniversalK.lean','/CodeSimulator.lean'))],'status_from_parent':'draft/pending audit; not assumed merged','required_adoption_action':'Compare final published candidate bodies/pins before adoption; only proof changes were inspected here.'}])
(O/'pending-family-overlap.json').write_text(json.dumps(overlap,indent=2)+'\n')
raw=Path('/private/tmp/ab34-ro1-integration/freeze-declarations.py').read_text();ns={};exec(raw[:raw.index('changed=[];removed=[]')],ns);extract=ns['extract']
rt='TCSlib/Complexity/TuringMachine/Build/RecordTable.lean';old=extract((O/'source-before'/(rt+'.txt')).read_text());new=extract((W/rt).read_text());oldmap={r['name']:r for r in old};row=next(r for r in native['owners'] if r['path']==rt);log=(O/row['receipt']).with_suffix('.log').read_text();warnings=[]
for l in log.splitlines():
 if "declaration uses 'sorry'" not in l:continue
 line=int(re.search(r'\.lean:(\d+):',l)[1]);r=max((r for r in new if r['line']<=line),key=lambda r:r['line']);b=oldmap[r['name']];assert b['full']==r['full']
 warnings.append({'path':rt,'name':r['name'],'current_warning_line':line,'baseline_line':b['line'],'whole_declaration_byte_identical':True,'baseline_and_current_whole_declaration_sha256':hashlib.sha256(r['full'].encode()).hexdigest(),'outside230_changed_new_roots':(rt,r['lexical_name']) not in mine})
assert len(warnings)==4 and all(r['outside230_changed_new_roots'] for r in warnings)
(O/'unchanged-RecordTable-sorry-warnings.json').write_text(json.dumps(warnings,indent=2)+'\n')
imports=json.loads((O/'final-held-imports.json').read_text());importlines='\n'.join('- `'+r['path']+'`' for r in imports)
report=f'''# RO1 CfgFacts-home held candidate

**Held for the import/home decision; not authorized to publish the import additions.**
The source worktree contains the complete uncommitted proposal. No commit, push, PR,
gate, canonical record change, screen, or full downstream replay was performed here.

The approved ruling is HANDOFF §3 item4: the generic
`Turing.MultiTapeTM.runFrom_one` lives in CfgFacts, replaces the Bool-only
`Turing.runFrom_one`, and every site, including colleague-owned sites, is repointed.
The new generic theorem and mechanical removals/repoints implement that ruling.
Eight direct CfgFacts imports are explicitly held proposals. The Simulation site
remains unchanged because the ruled home is above it in the dependency graph.
The requested Deterministic-home alternative is separate proposal work after this
folder freezes; nothing in this option adopts a revised home.

The baseline source pin is `9b5dcf46408db681bcbc721930ef2203fa6bc47d` (whole MAC8).
The assigned worktree HEAD is `8e5f2266b6ababbd0784f717e65a4903a0e3a0f0`, branch
`codex/ab34-runfrom-one`; its Lean tree equals that baseline commit. The actual
worktree is `/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4`.
`final-pins-and-worktree.json` records the read-only Git checks and exact dirty list.

The final patch changes60 owners:229 existing declaration bodies plus one new API,
and removes five old copies. Every retained declaration header is byte-identical.
The only changed definition body is `Turing.zr_cellContract`: only its `run` and
`env` proof fields change; every other field is byte-identical. The Bool public
copy and four private copies (`qy_run_one`, `xr_runFrom_one`, `satRed_one`,
`recordStep_runFrom_one`) are removed, and no former-name tokens remain.
The new API has no simp attribute. The positive explicit tactic-argument token
delta contains only the new theorem and `Nat.zero_add`, both theorem readers.

The eight precise import proposals are:

{importlines}

Every addition is exactly `import TCSlib.Complexity.TuringMachine.CfgFacts`.
No new hub import is proposed. The complete proposed graph is acyclic, and all
new consumer citations have API visibility. The eighth import was discovered by
the full closure preflight for ObliviousCandidate; earlier seven-import counts
are retained as preliminary artifacts and superseded by `final-held-imports.json`.

The remaining exact Simulation pair is `bufferedScanCfg_run`, baseline line1125.
The existing dependency path is CfgFacts → StateRenaming → Simulation, so the
reverse import cycles. The separately frozen witness is
`/private/tmp/ab34-ro1-simulation-cycle/` (manifest
`f5362cc8ec626d4ca9c8321a4e8b583d51fc4457f189ae09d20e18b2208a5dcb`).
No alternate API or home is introduced in this candidate to bypass it.

| Executed check | Result and bound |
|---|---|
| Final changed-owner native checks |60/60 exact final source hashes pass,0 errors;575 warnings, including4 unchanged RecordTable mathematical-sorry warnings outside the230 changed/new roots. |
| AX current/baseline |230 current roots /229 baseline roots; every existing root has exactly the same axiom set. No checked RO1 root reaches sorryAx. New API: propext, Quot.sound. |
| Complete new API doc/header/body native and sealed |Both pass,0 errors/warnings/sorries, under all6 ordinary reached foreign-definition guards. Imported theorem values are not traversed; projections/kernel abbreviations are classified separately. |
| Fresh opacity controls |12 actual kernel-checked positives pass; the exact same12 point/abstract controls fail sealed, with expected exit1 and12 intended rfl errors. Action.apply's default simp unfolding is removed in both variants. No unsafe reducibility or transparency override. |
| Header/definition/admission comparison |0 retained-header changes. One contract's2 proof fields only. Direct sorry-token counts unchanged across all929 TCSlib sources; the4 RecordTable warning declarations are byte-identical. |
| Snapshot provenance |Complete895-object private MAC8 clone; own target outputs unlinked before leanelab-o. All895 original MAC8 hashes unchanged; final whole private map retained. No splicing. |

Every elaboration used the approved wrapper, one own slot, local3/machine5,
four threads under nice10. Failed native/preparation attempts are preserved:
the first restricted wrapper could not access the shared lock and stopped before
Lean with exit130; subsequent proof failures exposed zero-plus-one simp matching
and fixed-time-two closures. The latter retain the outer successor equation and
cite the generic inner one-step equation. Corrected receipts are tied to the final
source SHA; failures are never counted as passes. Script assertions failed before
source writes and are preserved/disclosed in `failure-preparation-notes.json`.

`DECLARATION-DISPOSITIONS.md` enumerates all concrete changed/new declarations,
all five removals and the cycle obstruction. `fragment-dispositions.json` has301
fragment/revision rows, including refinements; that is not a copy count.
`uncapped-shape-dispositions.json` retains all970 lexical successor-equation
occurrences and140 parsed literal-one applications across929 sources, with
dispositions. Source capture/hash populations and listings are uncapped. These
shape searches, including inline calc/change/show/rfl/iterate-one/simp uses, are
candidate enumeration plus inspection, not a semantic exhaustiveness theorem.
Full original sources are in `source-before/`; final complete changed owners are
in `source-current/`, all as `.lean.txt`. `current-held-candidate.patch` is the
complete baseline-to-final diff. Intermediate captures/logs remain intact.

The pending FE/FH/CH7 drafts are not assumed merged. `pending-family-overlap.json`
maps known frozen roots and owner overlaps. In particular, SafeRun.cons is a
same-declaration overlap with CH7; root should preserve CH7's verified whole proof
when rebasing and reapply only any residual reader need. FH's three named roots
and CH7's five EmitIter facts/Hardness head-tail roots are unchanged by RO1.
Exact later remote-PR pin disjointness is not claimed without those final inputs.

The seven accepted SG1 structural kinds, FE-LIVE/FH1/BLIVE separation, the54-name
affected union (not54 copies), the bounded class-image residual, and the prior
nine inherited Primitives AX closures remain unchanged. The230-root AX result
does not convert those closures into direct admissions or establish global clear.
The remaining two-step rfl proof in CodePrefix and arbitrary-time/RProg/Oracle
variants are not literally the generic one-step statement and are retained.

Root owns the choice between this held-import option and any separately prepared
home revision, the final source commit, joint pending-family integration,
downstream replay on the then-current campaign tree, and audit/closure. The
consumer proofs were checked natively here; a full consumer opacity sweep or
post-other-PR merged-tree replay was not run or inferred.
'''
(O/'README.md').write_text(report)
print('Reports completed;4 unchanged RecordTable warnings verified; known family overlaps captured. Not frozen yet.')
