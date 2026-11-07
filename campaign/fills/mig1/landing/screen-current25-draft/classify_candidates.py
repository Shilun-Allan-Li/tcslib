"""Attach the source-read bounded dispositions to every one of the 60 new candidates."""
from pathlib import Path
import collections, json
p=Path(__file__).resolve().parent
groups=[
 ('G01',[1,6,25,39],'Loop terminal/startup composition proof',
  'Actual substantial proof overlap: decides/finds repeat startup run composition, computation packaging and the identical coefficient bound; emitting mode repeats the suffix. Reported to root for factoring. Not cleared by the candidate-count reduction.'),
 ('G02',[2,4],'Symmetric branch initial-configuration field calculations',
  'Two private constructor cases use the same Cfg.ext/Fin.addCases method with leftCfg versus rightCfg. Distinct fixed Bool/embedding cases, not a copied machine/host construction. The symmetric field-calculation template is disclosed, not granted a general debt waiver.'),
 ('G03',[3,7],'T3 selector contradiction template',
  'Five-line nonmembership proofs share 153 normalized characters, using different published selector equations; the triple case additionally uses j != i. The 12 former side proofs now call these two helpers. This small residual proof-method template remains explicit; no debt approval is inferred.'),
 ('G04',[5,11,18,24,33,34,35,40,48,49,55,57],'Moved forward-map parser phase relationships',
  'All endpoints have explicit deleted Catalog a2_map* origins. Some label-pair relations already existed in baseline; reader repairs push other phase/frame overlaps over the threshold. The backA/backB pair is a substantial retained mirrored rewind proof and remains a watch for disposition. Block already calls first; other matches include distinct append, emit, setup and frame operations using common readers. This is not a claim that all moved legacy redundancy is discharged.'),
 ('G05',[10,12,13,14,32,37,42,45,46,58],'Loop contract/export packaging',
  'Short witness wrappers and projections call the same loopHost_contracts/loopHostTM_* family. Long proofs reproduce their own public export call spelling and tuple packaging; they do not reimplement the exported operational proof. Distinguish these call-site matches from G01.'),
 ('G06',[9],'Rewind endpoint prefix in stronger head contract',
  'Both use the same published rewind_first_step and rewind_scan readers to select the concrete endpoint time. rewind_heads additionally proves the time bound and all-prefix head frame, which the weaker existential rewind_from_any omits. The common endpoint subderivation is disclosed; no global legacy reuse/debt clearance is asserted.'),
 ('G07',[15],'Branch-view transport plus let-header extraction',
  'timed_ledger has a depth-zero let V := by ... in its type; v3 includes that type tail in its extracted body. The shared text also includes short approved branch-k/State view normalization. This is not a copied second timed-ledger argument.'),
 ('G08',[31],'T5 canonical seam field scaffold',
  'Both endpoint proofs share Cfg.ext, canonical zero fields and destination-update normalization; the nontrivial clipping calculation is shared through catalog_buffer_clip. Transfer additionally clears the source. This is remaining field-proof scaffolding, not an additional copied sweep trace. It is disclosed without declaring every possible further factoring unnecessary.'),
 ('G09',[17],'Polynomial invariant versus setup-head induction',
  'Common runFrom_zero/initCfg and successor rewrite syntax appears in distinct invariants: polynomial bounded heads/tape contents versus setup stationary heads. Both consume the existing step/head facts; no duplicated operational theorem is identified from this short match.'),
 ('G10',[21,28,30,36,43,56,59],'T2 erased-bank specializations and phase contracts',
  'Depth-zero let B := ... in these theorem types makes v3 count specialized run/splitSafe statement tails as body text. Actual left/right erase proofs are only simpa using the one emitterP2_body_erase false/true proof. Length/compare use distinct existing call/phase facts; shared phase arguments and statement syntax are not a second erase proof.'),
 ('G11',[52],'T2 shared frame-core consumers',
  'Both private bank/admin frame helpers apply the existing emitterP2_frame core, then solve different selected-slot/unselected-slot obligations. v3 also includes the bank helper let-index type tail. Common Cfg field and Fin case scaffolding remains; the actual T2 consumer families now call their one helper each.'),
 ('G12',[8,16,23,41],'Direct pair-diagonal witness/spec corollaries',
  '71/79-character matches are short witness packages invoking the existing pairDiagTM_computes spec with coefficients 5 or 6, not rederived machines/computations. Catalog additionally needs its space clause; its zero-tape resource read remains an independent HOLD. No resource/API approval is inferred.'),
 ('G13',[20,22],'Visited-set/card-reader interface prefixes',
  'The two larger space proofs share only 111/114 characters with the 172-character redirect per-tape reader: spaceUsedByTape_eq_card plus visited-head membership/field correspondence syntax. Their operational ledgers and conclusions differ. This is common published-interface use, not a replay of the redirect run proof; the redirect home hold remains.'),
 ('G14',[26,38,44],'Moved setup-run induction template',
  'Each pair already existed with Catalog a2_mapSetup_run in baseline25. After the explicit move rename, the body difference is only its zero-case repair using public runFrom_zero/initCfg_eq. The inherited one-step-to-run induction pattern is disclosed, not newly authored operational content.'),
 ('G15',[29,47,50,51],'Moved tagged virtual-run induction template',
  'All four origin pairs already existed with Catalog a2_mapVirtual_run. After move renaming the only body change is an explicit runFrom_zero rewrite. Actual common content is a small tagged-step induction; it remains a real inherited proof template. Root separately commissioned invariant-route repoints after this frozen generation; none is applied in these raw inputs.'),
 ('G16',[19,27,53,54,60],'Canonical configuration data, including moved records',
  'These five syntactic term matches concern state/input/tape/head/output records, not proof copies. fwdMapCfg/fwdMapVirtual are exact old a2_mapCfg/a2_mapVirtual bodies after the explicit prefix rename; all five origin label pairs already existed. Their record layouts have distinct state tags, frozen tapes and output-prefix behavior. They are not newly copied transition tables.')]
rows=json.loads((p/'new-candidate-provenance.json').read_text())
by_id={r['id']:r for r in rows};assigned=[];summary=[]
for gid,ids,title,disposition in groups:
 selected=[]
 for number in ids:
  key=f'N{number:02d}';r=dict(by_id[key],group=gid,group_title=title,disposition=disposition)
  assigned.append(r);selected.append(r)
 summary.append({'group':gid,'title':title,'candidate_ids':[r['id'] for r in selected],
                 'directed_candidates':len(selected),'cross_file':sum(r['cross_file'] for r in selected),
                 'kinds':dict(collections.Counter(r['kind'] for r in selected)),
                 'disposition':disposition})
assert len(assigned)==len({r['id'] for r in assigned})==60
assert {r['id'] for r in assigned}==set(by_id)
assert sum(r['cross_file'] for r in assigned)==17
(p/'new-candidate-classifications.json').write_text(json.dumps(sorted(assigned,key=lambda r:r['id']),indent=2)+'\n')
(p/'classification-groups.json').write_text(json.dumps(summary,indent=2)+'\n')
lines=['# Bounded source classification of all 60 new directed candidates','',
       'Every new directed edge is assigned exactly once below. Full endpoints, original scores,',
       'source positions and explicit baseline origins are retained in',
       '`new-candidate-classifications.json`; these are source-read dispositions, not approvals.','',
       '| Group | IDs | Cross-file / total | Source classification |','| --- | --- | --- | --- |']
for r in summary:
 lines.append('| '+r['group']+' — '+r['title']+' | '+', '.join(r['candidate_ids'])+' | '+str(r['cross_file'])+' / '+str(r['directed_candidates'])+' | '+r['disposition']+' |')
(p/'semantic-review.md').write_text('\n'.join(lines)+'\n')
base={(r['target'],r['source']):r for r in json.loads((p/'base-all-candidates.json').read_text())}
head=json.loads((p/'head-all-candidates.json').read_text())
changed=[]
for r in head:
 old=base.get((r['target'],r['source']))
 if old and (old['shared_chars'],old['source_body_chars'])!=(r['shared_chars'],r['source_body_chars']):
  changed.append({'head':r,'base':old})
assert len(changed)==27
(p/'existing-changed-metrics.json').write_text(json.dumps(changed,indent=2)+'\n')
known=[]
for r in head:
 if {r['target'],r['source']}=={'Loop.lean::emCall_first_entry','Primitives.lean::emitter_first_entry'} or all(x.split('::')[1] in ['copyMapTM','transferMapTM','clearTM'] for x in [r['target'],r['source']]):
  known.append(r)
(p/'known-retained-candidates.json').write_text(json.dumps(known,indent=2)+'\n')
print(json.dumps({'classified_new':len(assigned),'new_cross_file':17,'new_in_file':43,
                  'groups':len(summary),'existing_changed_metrics':len(changed),
                  'known_retained_directed_candidates':len(known)},indent=2))
