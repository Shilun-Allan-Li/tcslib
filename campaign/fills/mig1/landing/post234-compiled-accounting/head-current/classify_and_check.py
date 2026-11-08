from pathlib import Path
import json,gzip,hashlib,collections,importlib.util,sys,re,datetime
sys.dont_write_bytecode=True
P=Path('/private/tmp/mig-post234-final-head-accounting');ctx=json.loads((P/'context.json').read_text());B=Path(ctx['baseline_frozen_folder']);R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,d):(P/n).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
head=json.loads((P/'map-head-complete.json').read_text());base=json.loads((B/'map-base-complete.json').read_text());bax=json.loads((B/'allax-base.json').read_text());delta=json.loads((P/'delta-base-head.json').read_text())
for n in base:base[n]['axioms']=bax[n]['axioms']
spec=importlib.util.spec_from_file_location('own_source',P/'source_roots.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
source={};named={}
for side in ['Base','Head']:
 rows=[]
 for owner in ctx['primary_owners']+ctx['context_owners']:
  path=owner.replace('.','/')+'.lean';text=((B/'source-captures/Base'if side=='Base'else P/'source-captures/Head')/(path+'.txt')).read_text()
  for r in mod.declarations(text,path):rows.append({k:r[k]for k in ['name','path','kind','private','line','end_line','chunk_sha256','commentless_tokens_sha256']})
 source[side]=rows;named[side]={(r['path'][:-5].replace('/','.'),r['name'],r['private']):r for r in rows}
 def classify(n,r):
  raw=n
  if r['private']:
   prefix='_private.'+r['owner']+'.';assert n.startswith(prefix),n
   rest=n[len(prefix):];idx,dot,raw=rest.partition('.');assert dot and idx.isdigit(),n
  row=named[side].get((r['owner'],raw,r['private']))
  if row:
   category='authored private source declaration'if r['private']else'authored nonprivate source declaration';return {'category':category,'source_name':raw,'source_kind':row['kind'],'source_path':row['path'],'source_line':row['line'],'source_chunk_sha256':row['chunk_sha256']}
  matches=[v for(owner,name,private),v in named[side].items()if owner==r['owner']and private==r['private']and raw.startswith(name+'.')];parent=max(matches,key=lambda v:len(v['name']))if matches else None
  return {'category':'generated or synthesized constant; no exact written named source declaration','source_name':None,'source_parent_name':None if parent is None else parent['name'],'source_parent_kind':None if parent is None else parent['kind'],'source_path':r['owner'].replace('.','/')+'.lean','internal_flag_is_not_a_source_API_classifier':True}
 mapped={n:classify(n,r)|{'name':n,'owner':r['owner'],'kind':r['kind'],'private':r['private'],'internal':r['internal'],'axioms':r['axioms'],'full_type_utf8_bytes':r['typeExprBytes'],'full_type_sha256':r['typeExprSHA256']}for n,r in(base if side=='Base'else head).items()}
 save('classified-census-'+side.lower()+'.json',mapped)
 save('source-named-'+side.lower()+'.json',rows)
source_delta={}
for label,current,opposite in [('added','Head','Base'),('removed','Base','Head')]:
 rows=[r for k,r in named[current].items()if k not in named[opposite]and k[0]in ctx['primary_owners']];source_delta[label]=rows;source_delta[label+'_public']=[r['name']for r in rows if not r['private']];source_delta[label+'_private']=sum(r['private']for r in rows)
classification={}
for label,side in [('added','head'),('removed','base')]:
 cm=json.loads((P/('classified-census-'+side+'.json')).read_text());classification[label]=[cm[n]for n in sorted(delta[label])];classification[label+'_categories']=dict(collections.Counter(r['category']for r in classification[label]));classification[label+'_nonprivate_categories']=dict(collections.Counter(r['category']for r in classification[label]if not r['private']))
classification['method']='Exact owner/privacy-qualified source names identify written declarations, preserving the actual private kernel prefix. Generated and synthesized constants are reported separately even when Lean marks them nonprivate/noninternal. No exact private ID normalization or proof-value comparison.';save('delta-classification-current.json',classification);save('source-named-delta.json',source_delta)
# Associate every changed raw type with its actual source/kernel classification.
cb=json.loads((P/'classified-census-base.json').read_text());ch=json.loads((P/'classified-census-head.json').read_text());typechanges=[]
for row in delta['shared_field_changes']['typeExprSHA256']:
 n=row['name'];typechanges.append(row|{'base_classification':cb[n],'head_classification':ch[n]})
save('all-shared-type-changes-classified.json',typechanges)
publicauth=[r['name']for r in typechanges if not head[r['name']]['private']and ch[r['name']]['source_name']is not None]
# Every retained current source-root descendant is accounted by exact current owner/CI/type map.
records=collections.defaultdict(list);complete=[]
for line in gzip.open(P/'Head-roots.out.gz','rt'):
 if line.startswith(('ROOTMAP|','ROOTDESC|','CITED|')):
  tag,j=line.split('|',1);records[tag].append(json.loads(j))
 elif line.startswith('ROOTCOMPLETE|'):complete.append(int(line.split('|',1)[1]))
requests=json.loads((P/'current-selected-source-roots.json').read_text());roots=records['ROOTMAP'];descs=records['ROOTDESC'];assert len(roots)==154 and complete==[154]and len({r['compiled_name']for r in roots})==154;assert{(r['owner'],r['source_name'],r['private'])for r in roots}=={(r['owner'],r['name'],r['private'])for r in requests['roots']}
selected={};std={'propext','Classical.choice','Quot.sound'}
for r in roots:
 n=r['compiled_name'];assert n in head and r['owner']==head[n]['owner']and r['private']==head[n]['private'];ds=[d for d in descs if d['root']==n];expected={k for k in head if k==n or k.startswith(n+'.')};assert{d['name']for d in ds}==expected
 for d in ds:
  k=d['name'];assert k in head and all(head[k][f]==d[f]for f in ['owner','kind','private','internal','axioms'])and set(d['axioms'])<=std;selected[k]=d
assert len(selected)==len(descs)==388
# Three unchanged RAM dependency closures are the only nonstandard ones. All seventeen targets standard.
nonstandard={n:r['axioms']for n,r in head.items()if not set(r['axioms'])<=std};assert set(nonstandard)=={'WordRAM.WordSizeComputable.mono','WordRAM.wordSizeComputable_logSpace','WordRAM.wordSizeComputable_of_spaceConstructible'}and all(base[n]['axioms']==v for n,v in nonstandard.items())
targets=json.loads((R/'campaign/fills/mig1/inputs/target-admissions.json').read_text());assert len(targets)==17
for r in targets:assert r['name']in selected and set(selected[r['name']]['axioms'])<=std
# The unchanged Finite context is compared in every full metadata field.
fn=[n for n,r in head.items()if r['owner']in ctx['context_owners']];assert len(fn)==59 and set(fn)=={n for n,r in base.items()if r['owner']in ctx['context_owners']}
fields=[k for k in base[fn[0]]if k not in ['typeExprArchive']]
for n in fn:assert all(base[n][k]==head[n][k]for k in fields),(n,[k for k in fields if base[n][k]!=head[n][k]])
save('current-root-native-records.json',dict(records));save('current154-selected-AX.json',{'source':ctx['source'],'actual_changed_roots':153,'conservative_selected_roots':154,'root_private':sum(r['private']for r in roots),'root_nonprivate':sum(not r['private']for r in roots),'descendants_additional':len(selected)-len(roots),'all_selected_constants':selected,'all_standard_or_subset':True,'distribution':dict(collections.Counter(','.join(r['axioms'])for r in selected.values())),'original17_all_selected_and_standard':True,'no_imported_theorem_value_traversal_or_proof_value_rendering':True})
summary=json.loads((P/'metadata-summary.json').read_text());summary['selected_root_AXIOMS_pending']=False;summary['actual_changed_source_roots']=153;summary['conservative_selected_roots']=154;summary['selected_plus_descendants']=388;summary['all388_standard_or_subset']=True;summary['Finite59_all_metadata_types_AX_exact']=True;summary['public_authored_shared_type_changes']=publicauth;summary['all3_remaining_RAM_nonstandard_exact_BASE']=True;summary['source_public_added']=source_delta['added_public'];summary['source_public_removed']=source_delta['removed_public'];save('metadata-summary.json',summary)
print(json.dumps({'current_changed':153,'selected_roots':154,'private_roots':sum(r['private']for r in roots),'nonprivate_roots':sum(not r['private']for r in roots),'selected_constants':len(selected),'additional_descendants':len(selected)-len(roots),'selected_AX_distribution':dict(collections.Counter(','.join(r['axioms'])for r in selected.values())),'source_public_added':source_delta['added_public'],'source_public_removed':source_delta['removed_public'],'public_authored_rawtype_changes':publicauth,'classified_adds':classification['added_categories'],'classified_removals':classification['removed_categories'],'classified_nonprivate_adds':classification['added_nonprivate_categories'],'classified_nonprivate_removals':classification['removed_nonprivate_categories']},indent=2))
