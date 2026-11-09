from pathlib import Path
import json,hashlib,datetime,shutil,re
B=Path(__file__).resolve().parent;R=Path('/private/tmp/ab34-nfe2-replay')
summary=json.loads((B/'COMPARISON-SUMMARY.json').read_text())
assert summary['selectedABIExactTypeUniverseMetadataAXSimpPass']and summary['nineChangedPrivateRootsExact']and summary['allOwnedAXstandardBoth']
assert summary['rawRemoved']==12 and summary['rawAdded']==0 and summary['rawSharedMetadataAXorStructuralFingerprintChanges']==9
base=json.loads((B/'BASE-ALL-OWNED-METADATA.json').read_text());head=json.loads((B/'HEAD-ALL-OWNED-METADATA.json').read_text())
bs=json.loads((B/'BASE-ABI-SELECTED.json').read_text());hs=json.loads((B/'HEAD-ABI-SELECTED.json').read_text())
assert len(bs)==len(hs)==50
bn={n for n,r in base.items()if not r['private']};hn={n for n,r in head.items()if not r['private']}
simpBase={n for n,r in base.items()if r['simp']};simpHead={n for n,r in head.items()if r['simp']}
unfoldBase={n for n,r in base.items()if r['unfold']};unfoldHead={n for n,r in head.items()if r['unfold']}
summary.update({'rawNonprivateNameSetExact':bn==hn,'rawNonprivateRemoved':sorted(bn-hn),'rawNonprivateAdded':sorted(hn-bn),'effectiveOwnedDefaultSimpLemmaSetsExact':simpBase==simpHead,'effectiveOwnedDefaultSimpLemmaCountBASE':len(simpBase),'effectiveOwnedDefaultSimpLemmaCountHEAD':len(simpHead),'effectiveOwnedDefaultUnfoldSetsExact':unfoldBase==unfoldHead,'effectiveOwnedDefaultUnfoldCountBASE':len(unfoldBase),'effectiveOwnedDefaultUnfoldCountHEAD':len(unfoldHead),'structuralFingerprintCaution':'Raw field typeStructuralHash64 records Lean Expr.hash. The API returns UInt64 but v4.25 Expr.Data.hash widens a cached UInt32. It is only a 32-bit change finder; matching fingerprints do not establish exact type equality. Exact Expr comparison is claimed only for the50 selected declarations.'})
assert summary['effectiveOwnedDefaultSimpLemmaSetsExact']and summary['effectiveOwnedDefaultUnfoldSetsExact']
(B/'COMPARISON-SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
targets=[]
for n,a in bs.items():
 if a['changedPrivateRoot']:
  b=hs[n];targets.append({'name':n,'userName':a['userName'],'owner':a['owner'],'BASE':a,'HEAD':b,'exactExprMatch':a['typeExpr']==b['typeExpr'],'universeParamsMatch':a['levelParams']==b['levelParams'],'AXnamesMatch':a['axioms']==b['axioms']})
assert len(targets)==9;(B/'TARGET9.json').write_text(json.dumps(targets,indent=2)+'\n')
integrity=[]
for phase,rows in [('BASE',bs),('HEAD',hs)]:
 for n,r in rows.items():
  expr=r['typeExpr'];bad=[q for q in ['...', '⋯', '…', 'Lean.Expr.mvar', 'Lean.Expr.fvar']if q in expr]
  integrity.append({'phase':phase,'name':n,'exactExpr_bytes':len(expr.encode()),'exactExpr_SHA256':hashlib.sha256(expr.encode()).hexdigest(),'unexpected_truncation_or_open_term_markers':bad})
assert not any(r['unexpected_truncation_or_open_term_markers']for r in integrity)
(B/'EXACT-EXPR-INTEGRITY.json').write_text(json.dumps({'selected_per_phase':50,'scope':'Full reprStr Expr values, not pretty-printer output; no source proof values rendered','rows':integrity},indent=2)+'\n')
core=Path('/Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Lean/Expr.lean')
data=core.read_bytes();(B/'bindings/Core-Lean-Expr.lean.txt').write_bytes(data)
(B/'bindings/STRUCTURAL-HASH-CAUTION.json').write_text(json.dumps({'raw_field':'typeStructuralHash64','API_return_type':'UInt64','actual_v4_25_data_hash':'Expr.Data.hash c = c.toUInt32.toUInt64; Expr.hash e = e.data.hash','effective_cached_bits':32,'role':'change finder only; no exact equality claim for omitted types','primary_source':str(core),'primary_source_SHA256':hashlib.sha256(data).hexdigest()},indent=2)+'\n')
for n in ['RESULT.json','request.json','module-results.json','object-accounting.json','source-before.json','input-before.json','input-after.json','output.json','static.txt','driver.py','down.txt']:
 p=R/n
 if p.is_file():shutil.copyfile(p,B/'bindings'/('passed157-'+n.replace('/','-')))
(B/'RUNS.json').write_text(json.dumps([{'label':d.name,**json.loads((d/'run.json').read_text()),'errorRows':len(re.findall(r': error(?:\(|:)',(d/'raw.out').read_text())),'countsAsSuccessfulCensus':d.name in ['02-BASE','03-HEAD']}for d in sorted((B/'attempts').iterdir())],indent=2)+'\n')
p=B/'PREPARATION.json';d=json.loads(p.read_text());d['status']='COMPLETED FRESH02-BASE/03-HEAD; initial fixture 01 excluded';d['structural_hash_limit']=summary['structuralFingerprintCaution'];p.write_text(json.dumps(d,indent=2)+'\n')
counts=summary['counts'];removed=json.loads((B/'RAW-REMOVED.json').read_text());changes=json.loads((B/'RAW-SHARED-CHANGES.json').read_text())
report=[]
report.append('# Compact four-owner ABI and axiom census: PASS within stated scope\n')
report.append('Fresh successful BASE/HEAD executions bind BASE 9b5dcf46408db681bcbc721930ef2203fa6bc47d/whole MAC8 and HEAD d64dff4fbef865d815c6a561ce8037ea1bae07a2/whole NFE2. HEAD import occurred only after the explicit 157/157 PASS result (failed 0/static 0/valid 895). The exact same corrected probe SHA256 30eb09efe78e43a60fa2554b123fd449fa60f6f1c5546972146706743cd78699 ran on both phases. Fresh rows are not reused from historical 11-root evidence. Root owns source/gate/readiness adoption.\n')
report.append('## Exact comparison scope\n')
report.append('All 50 selected declarations match full Lean Expr types, universe parameters, declaration metadata, complete dependency-axiom names and owned default-simp/unfold membership. The selection comprises all 41 nonprivate constant outside the confirmed internal generated proof-auxiliary cohort, plus exactly 9 changed private roots. Complete exact Expr and readable types are retained in BASE/HEAD-ABI-SELECTED and TARGET9. All 100 selected Expr records contain no truncation/open-term markers. Pretty text is a display aid; exact comparisons use the full reprStr Expr and universe lists. No theorem proof values are rendered.\n')
report.append('Full AX names and default simp/unfold membership are recorded for EVERY owned constant: BASE 2,573, HEAD 2,561. Every axiom set on both sides is a subset of propext/Classical.choice/Quot.sound; no sorryAx or other axiom occurs in this four-owner census. The effective owned simp lemma-name set is exactly 37 on both sides, and owned unfold sets are both empty. This is not a global library AX/simp claim.\n')
report.append('## Raw counts and exclusions\n')
report.append('| Phase | Owned | Raw nonprivate | Exact-type selected | Confirmed proof auxiliaries | Full types omitted |\n| --- | ---: | ---: | ---: | ---: | ---: |\n')
for phase in ['BASE','HEAD']:
 c=counts[phase];report.append(f"| {phase} | {c['raw']} | {c['rawNonprivate']} | {c['abiSelected']} | {c['excludedGeneratedProofAux']} | {c['typeOmitted']} |\n")
report.append('\nThe raw 105 nonprivate names are exact as a set. Of these, 64 per phase are internal proof auxiliaries whose full types are excluded, leaving 41 selected nonprivate constants. Their exclusion is not an assertion that their types were compared. Another 1,745 private constants outside the nine roots and generated-proof cohort have omitted full types on each side. Their full metadata/AX/default-simp rows remain present. Every excluded name and reason is enumerated.\n')
report.append('The proof-auxiliary classifier requires a numeric/underscore _proof_ name component, Lean internal-name status and a Prop type. No pattern hit fails those conditions, and the bounded lexical inventory of the eight complete source inputs finds no explicitly authored declaration name in that pattern. This is a documented compiler-helper classification, not a hidden exclusion based merely on private/public status.\n')
report.append('Raw field typeStructuralHash64 stores Lean Expr.hash. The v4.25 API returns UInt64 by widening its cached UInt32; it is a 32-bit change finder, not a cryptographic or exact type comparison. Full primary implementation source is retained. Equal fingerprints do not establish equality for the omitted private/generated types. There is expressly NO global owned-type equality claim.\n')
report.append('## Complete uncapped dispositions\n')
report.append('There are 12 removals, no additions, and 9 shared observed changes. All 21 rows are in the confirmed internal proof-auxiliary Prop cohort, are private, have standard-only AX sets and carry no owned simp/unfold membership. All shared declaration metadata is exact; the 9 shared rows have differing structural fingerprints, and 5 of them also drop Classical.choice from their AX closure. Full types for these excluded auxiliary rows were not rendered or exactly compared. RAW-REMOVED/ADDED/SHARED-CHANGES retain every row without a cap.\n')
report.append('| Operation | Full constant name | AX observation |\n| --- | --- | --- |\n')
for r in removed:report.append('| removed | `'+r['name']+'` | BASE standard only; no HEAD name |\n')
for r in changes:report.append('| shared fingerprint change | `'+r['name']+'` | '+('Classical.choice removed; standard only'if r['AXchanged']else'AX names exact; standard only')+' |\n')
report.append('\nEach changed generated name is nested beneath one of the nine authored changed roots. No non-generated name or selected ABI row changes in the observed raw metadata/AX/fingerprint comparison. This does not promote fingerprint equality of other private types into exact equality.\n')
report.append('## Execution and lineage\n')
report.append('All four complete BASE/HEAD source files, Git blobs, SHA256 and all 1,003 Lean source maps are retained. Only those four owner paths differ; InputLength is restored exactly to BASE. The replay source map is exactly HEAD across all 1,003 paths. Each census independently verifies its complete 895-object input against the guarded replay maps before import and verifies the full map unchanged afterward. The plain wrapper emits no oleans. Actual calls were serial through one shared helper slot, local 3/machine 5, j4/nice 10, with sourced env and Python3 -I managers. No source/Git/canonical/snapshot write or audit dispatch was made by this agent.\n')
report.append('The first BASE fixture 01 failed before emitting any census rows because String.drop already returns String. Its exact source/log/exit and unchanged 895 snapshots are retained and excluded from the comparison. Corrected BASE 02 and HEAD 03 separately exit 0/errors 0/complete counts; run durations are recorded. No failed compiled output or snapshot splice exists.\n')
report.append('The nine-root ordinary-definition guard packet and held-two typed formula packet remain immutable and separate. This compact census supports root’s final source review; it does not close a gate, decide held APIs, waive old debt, assert global type/AX equality, or establish merge readiness by itself. No further checks or own jobs remain at freeze.\n')
(B/'REVIEW.md').write_text(''.join(report))
# Human-reviewed disposition invariants are made executable here.
rootUsers={r['userName']for r in bs.values()if r['changedPrivateRoot']}
assert all(any((r['userName'].startswith(u+'._proof_'))for u in rootUsers)for r in removed)
assert all(any(n.split('.0.',1)[-1].startswith(u+'._proof_')for u in rootUsers)for n in [r['name']for r in changes])
assert sum(r['AXchanged']for r in changes)==5
print(json.dumps({'selected':50,'AX_owned_BASE':len(base),'AX_owned_HEAD':len(head),'rawNP_names_equal':bn==hn,'ownedSimp':len(simpBase),'ownedUnfold':len(unfoldBase),'removed':len(removed),'sharedChanges':len(changes),'sharedAXchanges':sum(r['AXchanged']for r in changes),'noGlobalTypeClaim':True}))
