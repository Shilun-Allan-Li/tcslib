"""Read-only byte restoration using a reviewer-authored decoder; no supplied programs."""
from pathlib import Path
import base64,gzip,hashlib,json
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
G=R/'campaign/gates/106-sg1-dedup';O=Path(__file__).resolve().parent
X=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-exchange/arora-barak-ch3-4/outbox/gates/106-sg1-dedup-r4-gate')
def sha(b):return hashlib.sha256(b).hexdigest()
def need(v,m):
    if not v:raise ValueError(m)
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
index=json.loads((X/'INPUT-INDEX.json').read_text());bundle=(X/'106-sg1-dedup-r4-bundle.md').read_bytes();physical={};pos=0
for ordinal,row in enumerate(index['entries']):
    if ordinal:pos+=1
    sec=bundle[pos:pos+row['section_bytes']];pos+=len(sec)
    header=('## ===== '+row['path']+' =====\n\n').encode();offset=len(header)+(4 if sec[len(header):].startswith(b'```\n') else 0)
    raw=sec[offset:offset+row['raw_bytes']];need(sha(raw)==row['raw_sha256'],'physical raw')
    physical[row['path']]=raw
prefix='campaign/gates/106-sg1-dedup/review/round4-publication-preparation/'
enc=json.loads(physical[prefix+'encoding-receipt-r4.json']);mapping={r['path']:r for r in enc['mappings']}
cache={}
def decode64(b):return base64.b64decode(b.split(b'base64:\n',1)[1] if b'base64:\n' in b else b)
def logical(n):
    if n in cache:return cache[n]
    if n in mapping:
        r=mapping[n];b=physical[r['render_path']]
        if r['codec']=='gzip+base64':b=gzip.decompress(decode64(b))
        elif r['codec']=='base64 of original gzip bytes':b=decode64(b)
        else:need(r['codec']=='identity UTF8','known codec')
        need(len(b)==r['bytes'] and sha(b)==r['sha256'],'current mapping '+n)
    else:b=physical[n]
    cache[n]=b;return b
for n in mapping:logical(n)
need(len(mapping)==570,'570 mappings')
old=json.loads(physical[prefix+'issued-r3-reconstruction.json']);hh=hashlib.sha256();total=0;oldrows=[]
for i,r in enumerate(old['rows']):
    b=logical(r['issued_bytes_binding']);need(len(b)==r['bytes'] and sha(b)==r['sha256'] and blob(b)==r['issued_blob'],'issued input '+r['path'])
    content=b if b.endswith(b'\n') else b+b'\n'
    if r['path'].endswith(('.lean','.py')):content=b'```\n'+content+b'```\n'
    section=('## ===== '+r['path']+' =====\n\n').encode()+content
    if i:hh.update(b'\n');total+=1
    hh.update(section);total+=len(section)
    oldrows.append({'ordinal':r['ordinal'],'path':r['path'],'bytes':len(b),'sha256':sha(b),'recorded_blob_exact':True})
need(len(oldrows)==1614 and total==100861434 and hh.hexdigest()=='104d4805fc8e1b53fdc8aa1e8ac7e611b09034398f46887fdc0be4d4e7aeb5d8','entire issued R3 bundle')
inherited=json.loads(physical[prefix+'inherited-r3-alias-verification.json'])
for r in inherited['transforms']:
    raw=gzip.decompress(decode64(logical(r['encoding_path'])));a=r['original']
    need(len(raw)==a['bytes'] and sha(raw)==a['sha256'],'old40 restoration '+a['path'])
for r in inherited['binary_companions']:
    raw=decode64(logical(r['represented_by']));need(len(raw)==r['bytes'] and sha(raw)==r['sha256'],'old binary companion')
result={'result':'PASS data-only restoration','all570_mappings_verified':True,'issued_R3_sections':len(oldrows),'issued_R3_bundle_bytes':total,'issued_R3_bundle_SHA256':hh.hexdigest(),'all_original_recorded_blob_identities_exact':True,'inherited_transforms':len(inherited['transforms']),'inherited_unique_carriers':len({r['encoding_path'] for r in inherited['transforms']}),'binary_companions':len(inherited['binary_companions']),'raw_bytes_restored_do_not_assert_new_Git_tree_query':True,'no_supplied_program_or_Lean_screen_execution':True}
(O/'retention-checks.json').write_text(json.dumps(result,indent=2)+'\n')
(O/'all1614-restored-inputs.json').write_text(json.dumps(oldrows,indent=2)+'\n')
print(json.dumps(result))
