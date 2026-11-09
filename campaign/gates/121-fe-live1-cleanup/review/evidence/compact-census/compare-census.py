from pathlib import Path
import json,hashlib,re,sys,datetime
B=Path(__file__).resolve().parent
labels={'BASE':sys.argv[1],'HEAD':sys.argv[2]}
standard={'propext','Classical.choice','Quot.sound'}
phases={};counts={}
for phase,label in labels.items():
 d=B/'attempts'/label;run=json.loads((d/'run.json').read_text());assert run['exit']==0 and run['whole895_snapshot_unchanged']
 raw=(d/'raw.out').read_text();assert not re.search(r': error(?:\(|:)',raw)
 rows=[json.loads(l.split('COMPACT|',1)[1])for l in raw.splitlines()if l.startswith('COMPACT|')]
 complete=[json.loads(l.split('COMPLETE|',1)[1])for l in raw.splitlines()if l.startswith('COMPLETE|')]
 assert len(complete)==1
 summary=complete[0];assert len(rows)==summary['rawOwned']
 byname={r['name']:r for r in rows};assert len(byname)==len(rows)
 assert sum(r['abiSelected']for r in rows)==summary['abiSelected']
 assert sum(r['changedPrivateRoot']for r in rows)==summary['changedRoots']==9
 assert not any(r['changedPrivateRoot']and not r['private']for r in rows)
 assert sum(not r['private']for r in rows)==summary['rawNonprivate']
 assert all(('typeExpr'in r)==r['abiSelected']for r in rows)
 assert all('typePretty'in r for r in rows if r['abiSelected'])
 assert all(isinstance(r['axioms'],list)and len(r['axioms'])==len(set(r['axioms']))for r in rows)
 owners=sorted({r['owner']for r in rows});assert len(owners)==4
 phases[phase]=byname
 selected={n:r for n,r in byname.items()if r['abiSelected']}
 compact={n:{k:v for k,v in r.items()if k not in ['typeExpr','typePretty']}for n,r in byname.items()}
 (B/(phase+'-ALL-OWNED-METADATA.json')).write_text(json.dumps(compact,indent=2)+'\n')
 (B/(phase+'-ABI-SELECTED.json')).write_text(json.dumps(selected,indent=2)+'\n')
 (B/(phase+'-AXIOM-SETS.json')).write_text(json.dumps({n:r['axioms']for n,r in byname.items()},indent=2)+'\n')
 (B/(phase+'-DEFAULT-SIMP.json')).write_text(json.dumps({n:{'simp':r['simp'],'unfold':r['unfold']}for n,r in byname.items()},indent=2)+'\n')
 (B/(phase+'-TYPE-EXCLUSIONS.json')).write_text(json.dumps([{'name':n,'owner':r['owner'],'private':r['private'],'internal':r['internal'],'kind':r['kind'],'typeIsProp':r['typeIsProp'],'generatedProofPattern':r['generatedProofPattern'],'excludedGeneratedProofAux':r['excludedGeneratedProofAux'],'reason':r['typeOmissionReason'],'structuralHash64':r['typeStructuralHash64']}for n,r in byname.items()if not r['abiSelected']],indent=2)+'\n')
 ownerCounts={}
 for o in owners:
  rr=[r for r in rows if r['owner']==o]
  ownerCounts[o]={'raw':len(rr),'private':sum(r['private']for r in rr),'nonprivate':sum(not r['private']for r in rr),'abiSelected':sum(r['abiSelected']for r in rr),'selectedChangedPrivateRoots':sum(r['changedPrivateRoot']for r in rr),'excludedGeneratedProofAux':sum(r['excludedGeneratedProofAux']for r in rr),'excludedNonprivateGeneratedProofAux':sum(r['excludedGeneratedProofAux']and not r['private']for r in rr),'otherOmittedPrivate':sum(r['private']and not r['abiSelected']and not r['excludedGeneratedProofAux']for r in rr),'defaultSimpLemmas':sum(r['simp']for r in rr),'defaultSimpUnfolds':sum(r['unfold']for r in rr),'nonstandardAX':[r['name']for r in rr if not set(r['axioms'])<=standard]}
 counts[phase]={'raw':len(rows),'rawNonprivate':summary['rawNonprivate'],'abiSelected':len(selected),'selectedChangedPrivateRoots':9,'excludedGeneratedProofAux':sum(r['excludedGeneratedProofAux']for r in rows),'excludedNonprivateGeneratedProofAux':sum(r['excludedGeneratedProofAux']and not r['private']for r in rows),'typeOmitted':sum(not r['abiSelected']for r in rows),'proofPatternNotConfirmed':[r['name']for r in rows if r['generatedProofPattern']and not r['excludedGeneratedProofAux']],'nonstandardAX':{r['name']:sorted(set(r['axioms'])-standard)for r in rows if not set(r['axioms'])<=standard},'owners':ownerCounts,'actual_run':str((d/'run.json').relative_to(B))}
base=phases['BASE'];head=phases['HEAD'];bn=set(base);hn=set(head);shared=sorted(bn&hn)
metadata_keys=['owner','userName','kind','private','internal','levelParams','valuePresent','unsafe','partial','kernelHints','reducibility','simp','unfold','protected','instancePriority','typeIsProp','generatedProofPattern','excludedGeneratedProofAux','changedPrivateRoot','abiSelected']
selectedBase={n for n,r in base.items()if r['abiSelected']};selectedHead={n for n,r in head.items()if r['abiSelected']}
abi=[]
for n in sorted(selectedBase&selectedHead):
 a=base[n];b=head[n];metadataDiff={k:{'BASE':a[k],'HEAD':b[k]}for k in metadata_keys if a[k]!=b[k]}
 abi.append({'name':n,'owner':a['owner'],'private':a['private'],'changedPrivateRoot':a['changedPrivateRoot'],'exactExprMatch':a['typeExpr']==b['typeExpr'],'universeParamsMatch':a['levelParams']==b['levelParams'],'metadataDifferences':metadataDiff,'axiomNamesMatch':a['axioms']==b['axioms'],'defaultSimpMatch':a['simp']==b['simp']and a['unfold']==b['unfold'],'BASE_typeExpr_SHA256':hashlib.sha256(a['typeExpr'].encode()).hexdigest(),'HEAD_typeExpr_SHA256':hashlib.sha256(b['typeExpr'].encode()).hexdigest()})
(B/'ABI-EXACT-COMPARISON.json').write_text(json.dumps(abi,indent=2)+'\n')
removed=[base[n]for n in sorted(bn-hn)];added=[head[n]for n in sorted(hn-bn)];changes=[]
for n in shared:
 a=base[n];b=head[n];md={k:{'BASE':a[k],'HEAD':b[k]}for k in metadata_keys if a[k]!=b[k]};ax=a['axioms']!=b['axioms'];fp=a['typeStructuralHash64']!=b['typeStructuralHash64'];expr=(a.get('typeExpr')!=b.get('typeExpr')) if a['abiSelected']and b['abiSelected']else None
 if md or ax or fp or expr:
  changes.append({'name':n,'owner':a['owner'],'metadataDifferences':md,'AXchanged':ax,'BASE_AXIOMS':a['axioms'],'HEAD_AXIOMS':b['axioms'],'allAXstandard':set(a['axioms'])<=standard and set(b['axioms'])<=standard,'typeStructuralHash64Changed':fp,'BASE_typeStructuralHash64':a['typeStructuralHash64'],'HEAD_typeStructuralHash64':b['typeStructuralHash64'],'exactExprCompared':a['abiSelected']and b['abiSelected'],'exactExprChanged':expr,'confirmedGeneratedProofAuxBoth':a['excludedGeneratedProofAux']and b['excludedGeneratedProofAux'],'private':a['private'],'internal':a['internal']})
(B/'RAW-REMOVED.json').write_text(json.dumps(removed,indent=2)+'\n');(B/'RAW-ADDED.json').write_text(json.dumps(added,indent=2)+'\n');(B/'RAW-SHARED-CHANGES.json').write_text(json.dumps(changes,indent=2)+'\n')
allDeltaGenerated=all(r['excludedGeneratedProofAux']for r in removed+added)and all(r['confirmedGeneratedProofAuxBoth']for r in changes)
abiPass=selectedBase==selectedHead and all(r['exactExprMatch']and r['universeParamsMatch']and not r['metadataDifferences']and r['axiomNamesMatch']and r['defaultSimpMatch']for r in abi)
nonstd=counts['BASE']['nonstandardAX']or counts['HEAD']['nonstandardAX']
summary={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'actualFreshBASE_HEAD':True,'source':json.loads((B/'bindings/source-bindings.json').read_text()),'counts':counts,'selectedABINameSetExact':selectedBase==selectedHead,'selectedABIRemoved':sorted(selectedBase-selectedHead),'selectedABIAdded':sorted(selectedHead-selectedBase),'selectedABIExactTypeUniverseMetadataAXSimpPass':abiPass,'selectedABICompared':len(abi),'nineChangedPrivateRootsExact':all(r['exactExprMatch']and r['universeParamsMatch']and not r['metadataDifferences']and r['axiomNamesMatch']and r['defaultSimpMatch']for r in abi if r['changedPrivateRoot'])and sum(r['changedPrivateRoot']for r in abi)==9,'allOwnedAXstandardBoth':not nonstd,'rawRemoved':len(removed),'rawAdded':len(added),'rawSharedMetadataAXorStructuralFingerprintChanges':len(changes),'allObservedRawDeltasInConfirmedInternalProofAuxCohort':allDeltaGenerated,'proofValuesRendered':False,'exactTypeComparisonScope':'Every selected nonprivate outside confirmed generated proof-auxiliary cohort plus9 private changed roots. No full exact Expr comparison of other private/generated types. StructuralHash64 is a change finder, not evidence of exact type equality.','noGlobalTypeEqualityClaim':True,'noGlobalAxiomClaim':True,'rootOwnsGateReadiness':True}
(B/'COMPARISON-SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k]for k in ['actualFreshBASE_HEAD','selectedABICompared','selectedABIExactTypeUniverseMetadataAXSimpPass','nineChangedPrivateRootsExact','allOwnedAXstandardBoth','rawRemoved','rawAdded','rawSharedMetadataAXorStructuralFingerprintChanges','allObservedRawDeltasInConfirmedInternalProofAuxCohort']}))
