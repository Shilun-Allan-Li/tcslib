#!/usr/bin/env python3
"""PHFE Rule 10 text-only snapshot preparation; never starts Lean, lake, Git or a shell.
Pinned tools stay byte-identical. Native collector/control results remain pending.
"""
from __future__ import annotations
import argparse, ast, collections, csv, datetime, hashlib, importlib.util, json, re, sys
from pathlib import Path

BASE = '5ed465f62e4ae0f93ded1a1ba49e807591b589eb'
TOOLS_PIN = 'bc9d982b83cb35ea351e2fb373752e8688945b1c'
FE = 'TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption'
PAIR = 'TCSlib/Cryptography/Pairing'
DECL = re.compile(r'^(?P<mods>(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*)'
                  r'(?P<kind>theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom)'
                  r'\b\s*(?P<name>[^\s(:{\[]*)')


def sha(raw): return hashlib.sha256(raw).hexdigest()
def dump(path, obj): path.write_text(json.dumps(obj, indent=2, ensure_ascii=False)+'\n')
def load_reviewed(path, name):
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
    return m


def head_from_metadata(root):
    dotgit = root/'.git'
    gd = dotgit if dotgit.is_dir() else Path(dotgit.read_text().strip().split(': ', 1)[1])
    if not gd.is_absolute(): gd = (root/gd).resolve()
    common = gd
    if (gd/'commondir').exists(): common = (gd/(gd/'commondir').read_text().strip()).resolve()
    text = (gd/'HEAD').read_text().strip()
    if re.fullmatch(r'[0-9a-f]{40}', text): return {'head':text, 'gitdir':str(gd), 'ref':None}
    ref = text.removeprefix('ref: ')
    for folder in [gd, common]:
        if (folder/ref).exists(): return {'head':(folder/ref).read_text().strip(), 'ref':ref,
                                         'gitdir':str(gd)}
        packed = folder/'packed-refs'
        if packed.exists():
            for line in packed.read_text().splitlines():
                if line.endswith(' '+ref): return {'head':line.split()[0], 'ref':ref,
                                                   'gitdir':str(gd)}
    raise RuntimeError('Cannot resolve HEAD metadata without Git; specify a valid worktree')


def owned_paths(root):
    paths = [root/(FE+'.lean'), *(root/FE).rglob('*.lean')]
    paths += [root/PAIR/'Exponents.lean', root/PAIR/'Linear.lean', root/PAIR/'MatrixDH.lean']
    paths += list((root/PAIR/'MatrixDH').rglob('*.lean'))
    return sorted({p for p in paths if p.is_file()})


def declarations(raw, path, blank):
    lines = raw.splitlines(); masked = blank(raw).splitlines()
    scopes=[]; ns=[]; rows=[]; anon=0
    for i,line in enumerate(masked):
        m=re.match(r'^namespace\s+(\S+)',line)
        if m:
            parts=m[1].split('.'); ns.extend(parts); scopes.append(('ns',len(parts))); continue
        if re.match(r'^(?:noncomputable\s+)?section\b',line): scopes.append(('sec',0)); continue
        if re.match(r'^end(?:\s|$)',line):
            if scopes:
                kind,n=scopes.pop()
                if kind=='ns': del ns[len(ns)-n:]
            continue
        m=DECL.match(line)
        if not m: continue
        name=m['name']; kind=m['kind']; anonymous=False
        if kind=='instance' and not name:
            anon+=1; name=f'<anonymous-instance-{anon}>'; anonymous=True
        if not name: continue
        full=name.removeprefix('_root_.') if name.startswith('_root_.') else '.'.join(ns+[name])
        rows.append({'name':full,'short_name':name.split('.')[-1], 'kind':kind,
                     'private':'private' in m['mods'].split(), 'anonymous':anonymous,
                     'module':path[:-5].replace('/','.'),'path':path,'line':i+1})
    for idx,r in enumerate(rows):
        r['end_line']=rows[idx+1]['line']-1 if idx+1<len(rows) else len(lines)
        text='\n'.join(lines[r['line']-1:r['end_line']])
        # Text only; canonical collector records and native reader validation are authoritative.
        statement=text.split(':=',1)[0]
        r['text']=text; r['statement']=statement
        r['body_sha256']=sha(text.encode())
    return rows


def normalize(s): return re.sub(r'[_\W]','',s).lower()
def choose_reader(target, theorems):
    t=target['name']; short=target['short_name']; norm=normalize(short)
    candidates=[]
    for r in theorems:
        rs=r['short_name']; rn=normalize(rs)
        if r['private']: continue
        rank=None
        if r['name'] in [t+'_eq',t+'_iff',t+'_def']: rank=0
        elif rs in [short+'_eq',short+'_iff',short+'_def']: rank=1
        elif rn in [norm+'eq',norm+'iff',norm+'def']: rank=2
        elif rn.startswith(norm) and rn!=norm: rank=3
        elif short in r['statement'] and re.search(r'(eq|iff|apply|zero|one|run|toRaw)',rs): rank=5
        if rank is None: continue
        if r['module']==target['module']: rank-=0.25
        if r['name'].rsplit('.',1)[0]==t.rsplit('.',1)[0]: rank-=0.25
        # Prefer an equation case over a substantive semantic/security theorem.
        if rs.endswith(('_eq','_iff','_def','_apply','_zero','_one','_toRaw','_coins')): rank-=0.2
        candidates.append((rank, len(r['statement']), r['name'], r))
    candidates.sort(key=lambda x:x[:3])
    return ([{'name':r['name'],'module':r['module'],'path':r['path'],'line':r['line'],
              'selection_score':rank} for rank,_,_,r in candidates[:8]])


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=Path,required=True); ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--tools',type=Path)
    args=ap.parse_args(); root=args.root.resolve(); out=args.out.resolve(); out.mkdir(parents=True,exist_ok=True)
    if out.is_relative_to(root/'TCSlib'): raise RuntimeError('Output may not be library source')
    tools=(args.tools or root/'evidence/preparation/tools').resolve()
    provenance_table=tools.parent/'tool-provenance.tsv'
    with provenance_table.open() as handle:
        for row in csv.DictReader(handle,delimiter='\t'):
            assert row['source_commit']==TOOLS_PIN, 'Tool pin changed'
            target=tools.parent/row['delivered_path']
            assert target.is_file() and sha(target.read_bytes())==row['prepared_sha256'], str(target)
    lexer=load_reviewed(tools/'seal/review/archived-gate10-tools/scan_explicit.py','phfe_pinned_lexer')
    head=head_from_metadata(root); paths=owned_paths(root); originals={}
    allrows=[]; snapshots={}
    for p in paths:
        raw=p.read_bytes(); rel=p.relative_to(root).as_posix(); originals[p]=raw
        snapshots[rel]={'sha256':sha(raw),'bytes':len(raw),'module':rel[:-5].replace('/','.')}
        allrows+=declarations(raw.decode(),rel,lexer.blank)
    theorems=[r for r in allrows if r['kind'] in ['theorem','lemma']]
    controls=[]; interfaces=[]
    for r in allrows:
        if r['private'] or r['kind'] in ['theorem','lemma']: continue
        row={k:v for k,v in r.items() if k not in ['text','statement']}
        row['reader_candidates']=choose_reader(r,theorems)
        row['reader']=row['reader_candidates'][0]['name'] if row['reader_candidates'] else None
        row['status']='READER_CANDIDATE_NOT_NATIVE_VALIDATED' if row['reader'] else 'MISSING_READER'
        row['requested_pair']=r['kind'] in ('def','abbrev'); row['positive_verified']=None; row['negative_verified']=None
        row['source_sha256']=snapshots[r['path']]['sha256']; row['head_at_snapshot']=head['head']
        if r['kind'] in ['structure','class','inductive']:
            row['sensitivity']='INDUCTIVE_INTERFACE_REQUIRES_GENERATED_PROJECTION_CENSUS'
            interfaces.append(row)
        elif r['kind']=='abbrev': row['sensitivity']='ABBREV_NOTATION_PENDING_NATIVE_CLASSIFICATION'
        elif r['kind']=='instance': row['sensitivity']='INSTANCE_OR_PROOF_IRRELEVANCE_PENDING_NATIVE_CLASSIFICATION'
        else: row['sensitivity']='ORDINARY_DEFINITION_CANDIDATE'
        controls.append(row)
    # No Lean lookup is imitated: report text-only resolution hypotheses separately.
    defs={r['name']:r for r in allrows if r['kind'] not in ['theorem','lemma']}
    theorem_names={r['name'] for r in theorems}
    static_items=[]; generated=[]
    for rel,snap in snapshots.items():
        raw=originals[root/rel].decode(); module=snap['module']
        for item in lexer.inventory(raw):
            owner=next((r for r in allrows if r['path']==rel and
                        r['line']<=item['line']<=r['end_line']),None)
            headword=item['head']; eq=re.search(r'\.(?:eq_\d+|eq_def|eq_unfold|_sunfold|match_\d+)$',headword)
            candidates=[n for n in defs if n==headword or n.endswith('.'+headword)]
            classification='UNRESOLVED_TEXT_ONLY'
            if len(candidates)==1:
                classification=('OWNED_DEFINITION_TEXT_CANDIDATE' if defs[candidates[0]]['module']==module
                                else 'FOREIGN_OWNED_DEFINITION_TEXT_CANDIDATE')
            elif headword in theorem_names or any(n.endswith('.'+headword) for n in theorem_names):
                classification='THEOREM_NAME_TEXT_CANDIDATE'
            row={**item,'path':rel,'module':module,'owner':owner['name'] if owner else None,
                 'candidates':candidates,'classification':classification,'native_verified':False}
            static_items.append(row)
            if eq: generated.append(row)
    modules=[s['module'] for _,s in sorted(snapshots.items())]
    modules_file='\n'.join(modules)+'\n'; (out/'modules.txt').write_text(modules_file)
    template=(tools/'seal/review/NmCollect.template.lean').read_text()
    a=template.index('def owners : List Name := ['); b=template.index(']',a)
    collector=template[:a]+'def owners : List Name := [\n  '+',\n  '.join('`'+m for m in modules)+template[b:]
    collector=re.sub(r'^import TCSlib\S*\n','',collector,flags=re.M)
    collector=collector.replace('import Lean\n','import Lean\n'+''.join('import '+m+'\n' for m in modules),1)
    (out/'Collect.lean').write_text(collector)
    common={'status':'PREPARED_NOT_RUN','base':BASE,'head_at_snapshot':head['head'],
            'source_bytes_equal_head':False,'source_head_binding':'WORKING_BYTES_NOT_YET_HEAD_VERIFIED',
            'head_metadata':head,'root':str(root),'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'lean_processes_started':0,'lake_processes_started':0,'git_processes_started':0}
    dump(out/'snapshot.json',{**common,'files':snapshots,'module_count':len(modules),
                             'source_snapshot_sha256':sha(json.dumps(snapshots,sort_keys=True).encode())})
    marker={'head':head['head'],'snapshot_sha256':sha((out/'snapshot.json').read_bytes())}
    with (out/'Collect.lean').open('a') as handle:
        handle.write('\nrun_cmd IO.println '+json.dumps('PHFE_SNAPSHOT '+json.dumps(marker))+'\n')
    dump(out/'controls-coverage.json',{**common,'rows':controls,'interfaces':interfaces,
         'requested_public_entries':len(controls),'requested_pairs':sum(x['requested_pair'] for x in controls),
         'verified_pairs':0,'executed_pairs':0,'coverage_complete':False,
         'counts':dict(collections.Counter(x['status'] for x in controls)),
         'native_catalog_reconciliation':'PENDING_ALL_GENERATED_CONSTANTS_AND_READERS',
         'policy_instance_reader_exemption':'Parent clarified: instance docs/readers exempt; retained in inventory',
         'written_definition_pairs':sum(x['kind'] in ('def','abbrev') for x in controls)})
    fields=['name','kind','module','path','line','reader','status','sensitivity','source_sha256']
    (out/'controls-coverage.tsv').write_text('\t'.join(fields)+'\n'+'\n'.join(
        '\t'.join(str(x.get(k,'')) for k in fields) for x in controls)+'\n')
    dump(out/'missing-readers.json',{**common,'rows':[x for x in controls if not x['reader']]})
    dump(out/'static-explicit-scan.json',{**common,'items':static_items,'generated_equation_candidates':generated,
          'kind_resolution':'TEXT_ONLY_NATIVE_SCAN1_SCAN2_PENDING','pass':None})
    dump(out/'declarations-text.json',{**common,'rows':[{k:v for k,v in r.items() if k!='text'} for r in allrows]})
    provenance={str(p.relative_to(tools)):sha(p.read_bytes()) for p in sorted(tools.rglob('*')) if p.is_file()}
    dump(out/'tool-fingerprints.json',{'source_pin':TOOLS_PIN,'root':str(tools),'files':provenance,
          'modifications_by_this_preparation':0,'source_table':str(root/'evidence/preparation/tool-provenance.tsv')})
    # Do not publish stale bytes if parent touched a module during the snapshot.
    for p,raw in originals.items():
        if p.read_bytes()!=raw: raise RuntimeError('Source changed during snapshot; rerun: '+str(p))
    if head_from_metadata(root)['head']!=head['head']: raise RuntimeError('HEAD changed; rerun snapshot')
    print(json.dumps({'status':'PREPARED_NOT_RUN','modules':len(modules),'public_entries':len(controls),
                     'missing_readers':sum(x['reader'] is None for x in controls),
                     'head':head['head'],'source_bytes_equal_head':False,'verified_pairs':0}))

if __name__=='__main__': main()
