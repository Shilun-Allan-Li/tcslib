"""Independent, data-only return review. No delivered program is imported or executed."""
from pathlib import Path
from collections import Counter
from datetime import datetime, timezone
import base64, gzip, hashlib, json, re, sys
R = Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
G = R/'campaign/gates/106-sg1-dedup'
O = Path(__file__).resolve().parent
X = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-exchange/arora-barak-ch3-4/outbox/gates/106-sg1-dedup-r4-gate')
inputs, results = {}, {}
def sha(b): return hashlib.sha256(b).hexdigest()
def rb(p):
    p=Path(p); b=p.read_bytes(); inputs[str(p)]={'bytes':len(b),'sha256':sha(b)}; return b
def js(p): return json.loads(rb(p))
def need(v, message):
    if not v: raise ValueError(message)
def write(n,x): (O/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def blob(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def source(p,side='head'): return rb(G/'review/round4-source-screen25/inputs'/side/(p+'.txt'))
def chunk(s,n):
    m=re.search(r'(?m)^private lemma '+re.escape(n)+r'\b',s);need(m is not None,n+' declaration')
    a=s.rfind('/--',0,m.start());e=s.find('\n/--',m.end());need(a>=0 and e>0,n+' delimiters')
    return s[a:e].rstrip()
report=rb(G/'findings-r4.md');delivery=rb(Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-exchange/inbox/sg1-dedup-r4-findings.md'))
need(report==delivery and len(report)==25445 and sha(report)=='f860e27dcc62396bcc564b15e713af71a75ae02366816cc36ed172dadf1e38a7','verbatim report')
ids=[line.split(' | ')[0][2:] for line in report.decode().splitlines() if re.match(r'^\| (?:F\d+|N\d+) \|',line)]
need(ids==['F4','F1','F2','F3']+['N'+str(i) for i in range(1,24)],'all27 report rows')
results['returned_report']={'bytes':len(report),'sha256':sha(report),'verbatim_local_delivery':True,'rows':ids,'verdict':'PASS0/0/0/27'}
# Published physical sections: independent byte, framing, SHA-1 blob identity and JSON checks.
pub=js(G/'publication-r4.json');idx=js(X/'INPUT-INDEX.json');data=rb(X/'106-sg1-dedup-r4-bundle.md')
need(len(data)==79398827 and sha(data)==pub['bundle_sha256']==idx['bundle_sha256'],'published bundle bytes')
for line in rb(X/'SHA256SUMS').decode().splitlines():
    digest,name=line.split(None,1);name=name.lstrip('* ');need(sha(rb(X/name))==digest,'exchange checksum '+name)
need(rb(X/'BUNDLE-FILES.txt')==rb(G/'BUNDLE-FILES-r4.txt'),'physical ordered list')
physical={};pos=0;jcount=0
for row in idx['entries']:
    if pos:
        need(data[pos:pos+1]==b'\n','section separator');pos+=1
    n=row['path'];need(n not in physical,'unique physical path')
    section=data[pos:pos+row['section_bytes']];pos+=len(section)
    header=('## ===== '+n+' =====\n\n').encode();need(section.startswith(header),'section header '+n)
    raw=section[len(header):len(header)+row['raw_bytes']]
    need(section[len(header)+row['raw_bytes']:] == b'','section framing length '+n)
    need(len(raw)==row['raw_bytes'] and sha(raw)==row['raw_sha256'] and sha(section)==row['section_sha256'],'section hashes '+n)
    need(blob(raw)==row['blob'],'recorded source-tree blob identity '+n)
    if n.endswith('.json'):json.loads(raw);jcount+=1
    physical[n]=raw
need(pos==len(data) and len(physical)==1696 and jcount==672,'section and JSON counts')
results['publication']={'sections':len(physical),'bytes':len(data),'sha256':sha(data),'all4_exchange_checksums':True,'all_section_and_recorded_blob_ids':True,'JSON_sections_parsed':jcount,'Git_commands_run':False,'tree_membership':'recorded publication binding; root owns live Git verification'}
# Hash every payload in the principal frozen evidence folders; do not execute their scripts.
manifest_results=[]
for rel in ['review/round4-live-prefix-repair','review/round4-source-screen25','review/round4-compiled-and-seals','review/round3-return-review','review/round4-preparation-peer-review','evidence/replay-msg8','evidence/replay-msg9']:
    folder=G/rel;p=folder/'MANIFEST.json'
    if not p.exists():
        rows=[{'path':str(f.relative_to(folder)),'bytes':len(rb(f)),'sha256':sha(rb(f))} for f in sorted(folder.rglob('*')) if f.is_file()]
        manifest_results.append({'folder':rel,'payloads':len(rows),'manifest':'none; independently inventoried','rows':rows});continue
    m=js(p);rows=m if isinstance(m,list) else m['files']
    for a in rows:
        b=rb(folder/a['path']);need(len(b)==a['bytes'] and sha(b)==a['sha256'],'frozen payload '+str(folder/a['path']))
    manifest_results.append({'folder':rel,'manifest_sha256':sha(rb(p)),'payloads':len(rows),'all_exact':True})
C=R/'campaign/status/2026-11-08-f6-merge/context-validity'
m=js(C/'MANIFEST.json');m=m if isinstance(m,list) else m['files']
for a in m:
    b=rb(C/a['path']);need(len(b)==a['bytes'] and sha(b)==a['sha256'],'context manifest '+a['path'])
manifest_results.append({'folder':str(C.relative_to(R)),'manifest_sha256':sha(rb(C/'MANIFEST.json')),'payloads':len(m),'all_exact':True})
results['frozen_manifests']=manifest_results
# Current plaintext source captures, literal F4 reversal and all17 complete repaired chunks.
bind=js(G/'review/round4-publication-preparation/current-source-bindings.json')
for a in bind['files']:
    b=rb(R/a['capture']);need(len(b)==a['bytes'] and sha(b)==a['sha256'] and blob(b)==a['blob'],'source capture '+a['path'])
need(len(bind['files'])==50,'all50 sources')
for a in bind['files']:
    if a['side']=='head':need(physical[a['path']]==rb(R/a['capture']),'root source equals captured078 '+a['path'])
lineage=js(G/'review/round4-source-screen25/F4-source-lineage.json');reversal=[]
for a in lineage['repairs']:
    new=source(a['path']).decode();old=rb(G/'review/round3-return-review/source79'/(a['path']+'.txt')).decode()
    need(new.count(a['new_chunk'])==old.count(a['old_chunk'])==1,'unique F4 chunks')
    need(new.replace(a['new_chunk'],a['old_chunk'])==old,'F4 entire-file reverse '+a['name'])
    hn=a['new_chunk'].split('private lemma ',1)[1].split(':= by',1)[0]
    ho=a['old_chunk'].split('private lemma ',1)[1].split(':= by',1)[0]
    need(hn==ho and a['new_chunk'].split(':= by',1)[1].strip()=='exact Turing.MultiTapeTM.runFrom_state_ne_none_of_le tm c t ht','F4 exact header/forwarder')
    reversal.append({'path':a['path'],'name':a['name'],'complete_file_reversal_exact':True,'header_unchanged':True,'Bool_specialization_inclusive':True})
prior=js(G/'review/round4-compiled-and-seals/prior17-source-byte-identity.json');old17=[]
for a in prior['all17']:
    new=chunk(source(a['path']).decode(),a['name']);old=chunk(rb(G/'review/round3-return-review/source79'/(a['path']+'.txt')).decode(),a['name'])
    need(new==old and len(new.encode())==a['bytes'] and sha(new.encode())==a['sha256'],'prior17 '+a['name'])
    old17.append({'path':a['path'],'name':a['name'],'sha256':sha(new.encode()),'exact':True})
for p in ['TCSlib/Complexity/ClassNP/Tautology.lean','TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean','TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean']:
    need(source(p)==rb(G/'review/round3-return-review/source79'/(p+'.txt')),'unchanged otherPR '+p)
results['source']={'all50_capture_sizes_sha256_blob_ids':True,'all25_root_sections_equal078_captures':True,'F4':reversal,'all17':old17,'other3_PR_files_byte_identical79':True,'source_freeze':'Reviewed full recorded42 common proof changes/three private replacement pairs; no independent general Lean AST claim'}
# Recompute selected-owner comparison from the full indexed maps, not from summary booleans.
P=G/'review/round4-compiled-and-seals';B=js(P/'map-base.json')['census'];H=js(P/'map-head.json')['census'];std={'propext','Classical.choice','Quot.sound'}
nonB={n for n,v in B.items() if not v['private']};nonH={n for n,v in H.items() if not v['private']};need(nonB==nonH and len(nonH)==1351,'nonprivate names')
def norm(v):
    v=dict(v);v['type_repr']={k:v['type_repr'][k] for k in ['utf8_bytes','sha256']};return v
need(all(norm(B[n])==norm(H[n]) for n in nonH),'all nonprivate records exact')
added=sorted(H.keys()-B.keys());removed=sorted(B.keys()-H.keys());shared=B.keys()&H.keys()
need(len(B)==7101 and len(H)==7063 and len(added)==6 and len(removed)==44 and all(H[n]['private'] for n in added) and all(B[n]['private'] for n in removed),'all census/deltas')
typechanges=[n for n in shared if norm(B[n])['type_repr']!=norm(H[n])['type_repr']]
axchanges={n:{'before':B[n]['axioms'],'after':H[n]['axioms']} for n in shared if B[n]['axioms']!=H[n]['axioms']}
need(len(typechanges)==10 and all(H[n]['private'] for n in typechanges),'private generated type changes')
need(len(axchanges)==1 and 'clA5Pair_sizes' in next(iter(axchanges)),'one AX change')
need(set(next(iter(axchanges.values()))['before'])-set(next(iter(axchanges.values()))['after'])=={'Classical.choice'},'choice removal')
nonstdB={n:v['axioms'] for n,v in B.items() if set(v['axioms'])-std};nonstdH={n:v['axioms'] for n,v in H.items() if set(v['axioms'])-std}
need(nonstdB==nonstdH and len(nonstdH)==9 and all('Primitives' in H[n]['owner'] for n in nonstdH),'nine inherited dependency closures')
SB=js(P/'effective-simp-base.json');SH=js(P/'effective-simp-head.json');need(SB==SH and len(SH)==168,'all168 simp references')
AX=js(P/'current45-selected-AX.json');roots=AX['roots'];names={r['compiled_name'] for r in roots};allax=AX['all138_constants']
need(len(names)==45 and len(allax)==138 and len(allax.keys()-names)==93 and sum(r['private'] for r in roots)==40,'45roots93descendants')
dist=Counter(tuple(sorted(v['axioms'])) for v in allax.values());need(all(set(v['axioms'])<=std for v in allax.values()),'all138 standard subset')
results['compiler']={'counts':[len(B),len(H)],'private':[sum(v['private'] for v in B.values()),sum(v['private'] for v in H.values())],'nonprivate_exact':len(nonH),'effective_owned_simp_exact':len(SH),'added':added,'removed':removed,'shared_private_type_changes':typechanges,'shared_AXIOM_changes':axchanges,'inherited9_nonstandard_dependency_closures':nonstdH,'roots':45,'private_roots':40,'public_roots':5,'descendants':93,'selected_total':138,'AX_distribution':{','.join(k) or '(empty)':v for k,v in dist.items()},'raw_type_limit':'Complete archive hashes/CRC checked below; indexed types/metadata compared. No proof-value or whole imported-environment equality claimed.'}
# Independently decode all18 original binary outputs, including failed preparations, as inert data.
archives=[]
for a in js(P/'archive-verification.json')['archives']:
    z=rb(P/a['gzip']);b64=rb(P/a['base64']);need(base64.b64decode(b64)==z,'gzip carrier '+a['gzip'])
    hh=hashlib.sha256();total=0
    with gzip.open(P/a['gzip'],'rb') as f:
        for piece in iter(lambda:f.read(1048576),b''):hh.update(piece);total+=len(piece)
    need(total==a['raw_bytes'] and hh.hexdigest()==a['raw_sha256'],'raw gzip CRC/hash '+a['gzip'])
    archives.append({'gzip':a['gzip'],'raw_bytes':total,'raw_sha256':hh.hexdigest(),'lossless':True,'original_exit':a['exit']})
need(len(archives)==18,'all18 archives')
results['lossless_archives']={'archives':archives,'raw_bytes':sum(a['raw_bytes'] for a in archives),'not_executed':True}
# F4 exact scope/control identities from sources and actual raw diagnostics.
guards=js(P/'F4-instrumentation.json')['guard_union'];need(len(guards)==6,'six guards');controls=[]
for a in js(P/'F4-control-identities.json'):
    context=a['context'];ns=rb(P/f'F4-{context}-native.lean.txt').decode();ss=rb(P/f'F4-{context}-sealed.lean.txt').decode()
    stripped='\n'.join(line for line in ss.split('\n') if not line.startswith('attribute [local irreducible] '));need(stripped==ns,'native sealed exact guard removal')
    need(ss.index('attribute [local irreducible]')<ss.index('/-- Live endpoints'),'whole chunk opacity placement')
    name='sat_live_prefix' if context=='SAT' else 'clA5_live_prefix'
    actual=rb(P/(name+'.actual-chunk.lean.txt')).decode().strip();need(actual in ns and actual in ss,'exact F4 source chunk')
    need(all(g in ss for g in guards),'all6 context guards')
    for mode in ['native','sealed']:
        run=js(P/f'F4-{context}-controls-{mode}-run.json');raw=gzip.decompress(rb(P/f'F4-{context}-controls-{mode}.out.gz')).decode()
        need(run['exit']==(0 if mode=='native' else 1) and run['errors']==(0 if mode=='native' else 12),'control receipts '+context+mode)
        for identity in a['identities']:
            key='CONTROL|'+identity['definition']+'|'+identity['mode']+'|'
            need(raw.count(key+('PASS|kernelChecked='+identity['kernel_name'] if mode=='native' else 'FAIL'))==1,'exact control identity '+context+mode+key)
        if mode=='sealed':need(raw.count('error: RFL_CONTROL|')==12,'12exact negative errors '+context)
    for mode in ['native','sealed']:
        run=js(P/f'F4-{context}-{mode}-run.json');raw=gzip.decompress(rb(P/f'F4-{context}-{mode}.out.gz')).decode()
        need(run['exit']==run['errors']==run['sorry_warnings']==0 and '[propext, Quot.sound]' in raw,'F4 native sealed AX '+context+mode)
    controls.append({'context':context,'ordinary_guards':6,'kernel_positive_receipts':12,'exact_negative_failures':12,'negative_exit':1,'scope_native_and_sealed_exit':0})
results['F4_controls']={'contexts':controls,'positive_total':24,'negative_total':24,'projection_abbrev_exclusions':12,'simp_attributes_removed_as_literal_source':'Turing.Action.apply, Turing.Cfg.init, Turing.MultiTapeTM.initCfg','no_new_Lean_run':True}
# All current raw screen/index/delta rows are retained; do not rerun the tiling CLI.
S=G/'review/round4-source-screen25';bc=js(S/'base-candidates.json');hc=js(S/'head-candidates.json');bi=js(S/'base-index.json');hi=js(S/'head-index.json')
def ident(r):return tuple(r[k] for k in ['a','b','kind','cross_file'])
def measure(r):return tuple(r[k] for k in ['shared','denominator','printed_percent'])
bd={ident(a):measure(a) for a in bc};hd={ident(a):measure(a) for a in hc};need(len(bd)==len(bc) and len(hd)==len(hc),'unique screen rows')
delta={'new':len(hd.keys()-bd.keys()),'gone':len(bd.keys()-hd.keys()),'changed':sum(bd[k]!=hd[k] for k in bd.keys()&hd.keys())}
need(delta=={'new':2,'gone':30,'changed':13},'45deltas')
classes=js(S/'all-HEAD-candidate-classification.json')['rows'];need({ident(a['row']):measure(a['row']) for a in classes}==hd,'complete1991 classifications')
need({ident(a):measure(a) for a in bc if a['kind']=='term'}=={ident(a):measure(a) for a in hc if a['kind']=='term'},'259term rows unchanged')
need([len(bi),len(hi),len(bc),len(hc),sum(a['shared'] for a in bc),sum(a['shared'] for a in hc)]==[1956,1945,2019,1991,648202,646175],'screen counts')
results['screen']={'eligible_spans':[len(bi),len(hi)],'directed_candidates':[len(bc),len(hc)],'shared_characters':[sum(a['shared'] for a in bc),sum(a['shared'] for a in hc)],'delta':delta,'all_HEAD_classified':len(classes),'classification':dict(Counter(a['status'] for a in classes)),'term_edges_unchanged':sum(a['kind']=='term' for a in hc),'full_tiling_run':False,'lint_receipts':'Reviewed inherited153→153 actual style exit1 and unchanged campaign0FAIL/28WARN/28INFO; no new lint CLI'}
# Named accounting is a mixed-disposition union, not a current-copy census.
ac=js(S/'F4-named-kind-accounting.json');u49=set(ac['prior_named_affected_49']);u54=set(ac['prior_plus_FE_LIVE_1_named_affected_54']);host=js(G/'review/round3-host-accounting-addon/disjoint-accounting.json')
need(len(u49)==49 and len(u54)==54 and u49<=u54 and len(u54-u49)==5 and 'clA5_live_prefix' in u49,'54namedunion')
results['accounting']={'Hardness_named_affected':[35,49,54],'denominator':544,'added_FE_names':sorted(u54-u49),'F4_intersection':['clA5_live_prefix'],'54_over544_percent':100*54/544,'SAT_named_lower_bound':'34/270','source_declarations_deleted_by_F4':0,'is_duplicate_census':False}
# Replay rows, exact ordered graph closure, whole-map lineage and scoped object changes.
IG=js(C/'import-graphs.json');BIND=IG['bindings'];GRAPHS=IG['graphs'];OC=js(C/'owner-import-closures.json')
for a in OC['groups']:
    if a['group']!='sg1':continue
    owner_union=set()
    for v in a['owners']:
        closure=set(v['TCSlib_closure_including_owner']);need('TCSlib.Complexity.SpaceComplexity.Hierarchy' not in closure,'Hierarchy owner closure');owner_union|=closure
    need(len(owner_union) in {63,72},'complete SG1 union size')
replay=[];maps=[]
for generation,count,static,label,targets in [('msg8',329,66,'sg1_old_head',[p[:-5].replace('/','.') for p in js(S/'partition.json')['current_PR_Lean_files']]),('msg9',2,0,'sg1_new_head',['TCSlib.Complexity.SpaceComplexity.Hierarchy'])]:
    folder=G/'evidence'/('replay-'+generation);order=rb(folder/('order-'+generation+'.txt')).decode().splitlines();raw=rb(folder/('replay-'+generation+'.log')).decode()
    rows=re.findall(r'(?m)^(TCSlib/\S+) exit=(\d+) errors=(\d+) sorry=(\d+)$',raw)
    need([r[0] for r in rows]==order and len(rows)==count and all(r[1:3]==('0','0') for r in rows) and sum(int(r[3]) for r in rows)==static,'replayraw '+generation)
    launches=rb(folder/('replay-'+generation+'-launches.log')).decode();need(len(launches.splitlines())==count and launches.count('-j4')==count,'j4launches '+generation)
    staticraw=rb(folder/('replay-'+generation+'-static.txt')).decode().strip();need(staticraw==f'modules {count}, mismatches 0, static total {static}','staticreceipt '+generation)
    graph={n:[i for i in imps if i.startswith('TCSlib')] for n,imps in GRAPHS[BIND[label]['graph_sha256']].items() if n!='TCSlib'}
    reverse={}
    for n,imps in graph.items():
        for i in imps:reverse.setdefault(i,set()).add(n)
    down=set();todo=list(targets)
    while todo:
        n=todo.pop()
        if n in down:continue
        down.add(n);todo.extend(reverse.get(n,()))
    generated=[];seen=set()
    def visit(n):
        if n in seen:return
        seen.add(n)
        for i in sorted(graph[n]):
            if i in down:visit(i)
        generated.append(n.replace('.','/'))
    for n in sorted(down):visit(n)
    need(generated==order and len(graph)==929,'exact graph order '+generation)
    sm=js(folder/'snapshot-objects.json');ks=[k for k,v in sm.items() if isinstance(v,dict) and len(v)==895];need(len(ks)==2,'whole895maps '+generation)
    before,after=sm[ks[0]],sm[ks[1]];changed=sorted(n for n in before if before[n]!=after[n]);need(set(before)==set(after),'895sameobject names')
    need(all(n[:-6] in order for n in changed),'changedobjects closure '+generation)
    maps.append((before,after))
    replay.append({'generation':generation,'modules':count,'failed':0,'static_total':static,'mismatches':0,'effective_j4_launches':count,'complete_graph_modules_excluding_root':929,'exact_graph_order':True,'whole_input_output_objects':895,'changed_objects':changed})
need(maps[0][1]==maps[1][0],'MSG8output exactly MSG9input')
results['replay']={'generations':replay,'whole895_map_chain_exact':True,'driver_helpers_read_as_data':True,'Lean_replay_executed_here':False,'current_tip_mergeability':'Root independently checks current live PR/base and prospective merged tree; auditor df434 clearance is pinned, not authority.'}
results['limits']={'Lean_elaboration_native_seal_replay':False,'copy_screen_tiling':False,'fresh_lint_CLI':False,'supplied_program_execution':False,'Git_command_or_ref_index_mutation':False,'source_snapshot_cache_canonical_changes':False,'auditor_finite_model_numeric_counts':'Accepted as auditor-reported finite sanity; not independently rerun or treated as universal proof','raw_type_values':'Archived bytes/CRC verified; selected maps compared, no proof values traversed','failed_preparations_preserved':'All four upstream attempts remain failed; own read-only display IndexError is disclosed in PREPARATION-FAILURES.md.'}
results['checked_utc']=datetime.now(timezone.utc).isoformat()
write('checks.json',results);write('INPUTS.json',{'files':[{'path':n,**v} for n,v in sorted(inputs.items())]})
print(json.dumps({'status':'PASS data-only checks','report_rows':len(ids),'physical_sections':len(physical),'manifest_folders':len(manifest_results),'source_captures':50,'prior_chunks':len(old17),'nonprivate_exact':len(nonH),'simp_exact':len(SH),'controls':[24,24],'screen_candidates':[len(bc),len(hc)],'replay':[329,2],'new_Lean_or_screen':False}))
