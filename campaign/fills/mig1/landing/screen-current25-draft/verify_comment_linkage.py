"""After the two screens, verify final actual source has identical v3 declarations/bodies."""
from pathlib import Path
import ast, collections, datetime, hashlib, json, os, re, sys

p = Path(__file__).resolve().parent
root = p.parents[4]
assert all(json.loads((p/(label+'.json')).read_text())['exit']==0 for label in ['base','head'])
capture = json.loads((p/'capture.json').read_text())
paths = [r['path'] for r in capture['files']]
wt = Path(os.environ['TCSLIB_SCRATCH'])/'wt-epad'
source = (p/'copy-text-screen-v3.py.txt').read_text()
tree = ast.parse(source)
nodes = [n for n in tree.body if
         isinstance(n,ast.FunctionDef) and n.name in ['strip','scopes','qualify','body'] or
         isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id in ['DECL','SCOPE'] for t in n.targets)]
ns = {'re':re, 'sys':sys}
exec(compile(ast.Module(body=nodes,type_ignores=[]),'<reviewed-v3-comment-linkage>','exec'),ns)
basenames=collections.Counter(Path(x).name for x in paths)

def extract(path,raw):
    t=ns['strip'](raw)
    matches=list(ns['DECL'].finditer(t));events=ns['scopes'](path,t)
    all_rows=[];found=[]
    for i,m in enumerate(matches):
        end=matches[i+1].start() if i+1<len(matches) else len(t)
        body=re.sub(r'\s+','',ns['body'](t[m.start():end]))
        namespace=[n for o,n in events if o<=m.start()][-1]
        row=(m.group(3),ns['qualify'](namespace,m.group(3)),m.group(2),
             'proof' if m.group(2) in ['theorem','lemma'] else 'term',m.group(1).split(),body)
        all_rows.append(row)
        if len(body)>=60:found.append(row)
    short=collections.Counter(r[0] for r in found)
    qualified=collections.Counter(r[1] for r in found);seen=collections.Counter()
    screened=[]
    for row in found:
        name,qn,decl_kind,kind,flags,body=row
        if short[name]==1:key=name
        elif qualified[qn]==1:key=qn
        else:
            seen[qn]+=1;key=qn+'#'+str(seen[qn])
        filename=Path(path).name if basenames[Path(path).name]==1 else path
        screened.append((filename+'::'+key,kind,body))
    return all_rows,screened

before={path:(wt/path).read_bytes() for path in paths}
target=p/'comment-linkage'
target.mkdir()
rows=[];total_all=total_screened=0
for path in paths:
    prior=(p/'inputs/head'/(path+'.txt')).read_bytes()
    current=before[path]
    captured_all,captured_screened=extract(path,prior.decode())
    current_all,current_screened=extract(path,current.decode())
    assert captured_all==current_all,('all extracted declarations changed',path)
    assert captured_screened==current_screened,('screened labels/kinds/bodies changed',path)
    destination=target/'final-actual'/(path+'.txt')
    destination.parent.mkdir(parents=True,exist_ok=True);destination.write_bytes(current)
    total_all+=len(current_all);total_screened+=len(current_screened)
    rows.append({'path':path,'captured_sha256':hashlib.sha256(prior).hexdigest(),
                 'final_actual_sha256':hashlib.sha256(current).hexdigest(),
                 'bytes_differ':prior!=current,'all_extracted_count':len(current_all),
                 'screened_count':len(current_screened),
                 'names_namespaces_kinds_flags_normalized_bodies_equal':True,
                 'screen_labels_kinds_normalized_bodies_equal':True})
assert all((wt/path).read_bytes()==before[path] for path in paths),'source changed during final capture'
adoption=root/'campaign/fills/mig1/landing/comment-cleanup-adoption.json'
(target/'comment-cleanup-adoption.json').write_bytes(adoption.read_bytes())
result={'verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'read_only_parser_comparison':True,'tiling_runs_added':0,
        'raw_screen_inputs_remain_original_pre_comment_capture':True,
        'trusted_parser_sha256':hashlib.sha256(source.encode()).hexdigest(),
        'comment_adoption_receipt_sha256':hashlib.sha256(adoption.read_bytes()).hexdigest(),
        'source_count':len(paths),'all_extracted_declarations':total_all,
        'screened_declarations':total_screened,
        'current_sources_stable_during_verification':True,
        'all_comparisons_equal':True,'files':rows}
(target/'equivalence.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='files'},indent=2))
