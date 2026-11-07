"""Read immutable audit/pack evidence as data. No Git, Lean, or screen execution."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import sys

sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent
REPO=OUT.parents[4]
GATE=REPO/'campaign/gates/106-sg1-dedup'


def sections():
    d=json.loads((GATE/'dispatch.json').read_text())
    p=Path(os.environ['TCSLIB_EXCHANGE'])/'outbox/gates/106-sg1-dedup-gate/106-sg1-dedup-bundle.md'
    raw=p.read_bytes();assert len(raw)==d['bytes'] and hashlib.sha256(raw).hexdigest()==d['sha256']
    s=raw.decode();matches=list(re.finditer(r'^## ===== (.+) =====\n',s,re.M))
    names=[m[1] for m in matches]
    assert len(names)==len(set(names))==d['sections']==166
    index=(p.parent/'BUNDLE-FILES.txt').read_text().splitlines()
    assert names==index
    data={}
    for i,m in enumerate(matches):
        block=s[m.end():matches[i+1].start() if i+1<len(matches) else len(s)].strip('\n')
        if block.startswith('```\n') and block.endswith('\n```'):block=block[4:-4]
        data[m[1]]=block+'\n'
    return d,data


def main():
    audit=(OUT/'findings.received.md').read_bytes()
    assert len(audit)==9822 and hashlib.sha256(audit).hexdigest()=='f6263c500ec7496a8867b7652bd44a1dbc423bd2711d5c6268a40347332b058c'
    dispatch,sec=sections()
    tool=REPO/'campaign/fills/mig1/review/checkpoint05-2026-11-07/compare.py'
    spec=importlib.util.spec_from_file_location('independent_decl_reader',tool)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    population=(GATE/'evidence/current/screen/population-head.txt').read_text().splitlines()
    sources={f:sec[f] for f in population}
    all_decl={f:mod.decls(s) for f,s in sources.items()}
    scopes={f:{d['name']:d for d in ds} for f,ds in all_decl.items()}
    sat='TCSlib/Complexity/ClassNP/SAT.lean';hard='TCSlib/Complexity/CookLevin/Hardness.lean'
    basic='TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean'
    wanted={sat:['sat_guard_add','SatClean','satStopTM','satPadCfg','satMapTM','satPadAction','satStopCfg','sat_bridge_bound'],
            hard:['clA5_guard_add','CLA5Clean','clA5StopTM','clA5PadCfg','clA5MapTM','clA5PadAction','clA5StopCfg','clA5_bridge_bound'],
            basic:['Segment.trans','Segment.zero','Segment.mono','segment_iff','Segment'],
            'TCSlib/Complexity/ClassNP/Tautology.lean':['tautDualSegment','tautDualSegment_iff_segment'],
            'TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean':['counterSpan','counterSpan_iff_segment'],
            'TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean':['DGSpan','dgSpan_iff_segment']}
    quotes=[];details={}
    for f,names in wanted.items():
        details[f]=[]
        lines=sources[f].splitlines()
        for n in names:
            matches=[d for d in all_decl[f] if d['name']==n or d['name'].endswith('.'+n)]
            assert len(matches)==1,(f,n,[d['name'] for d in matches])
            d=matches[0]
            last=d['start']-1+max(i+1 for i,l in enumerate(d['code'].splitlines()) if l.strip())
            # Include an adjacent docstring when present; record code and total span separately.
            before='\n'.join(lines[:d['start']-1]).rstrip()
            start=d['start']
            if before.endswith('-/'):
                j=before.rfind('/--')
                if j>=0 and before.find('-/',j)==len(before)-2:start=before.count('\n',0,j)+1
            details[f].append(dict(name=d['name'],kind=d['kind'],private=d['private'],
                                   declaration_line=d['start'],span_start=start,span_end=last,
                                   span_lines=last-start+1,header=d['header'],code=d['code'].rstrip()))
            quotes.append(f'## {f}:{start}–{last}\n\n```lean\n'+'\n'.join(f'{i+1}: {lines[i]}' for i in range(start-1,last))+'\n```\n')
    (OUT/'source-quotes.md').write_text('\n'.join(quotes))
    replay=json.loads((GATE/'evidence/current-after-natbits/receipt.json').read_text())
    blobchecks=[]
    for row in replay['audited_scope']:
        b=sources[row['path']].encode()
        blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        assert blob==row['audited_blob']==row['current_blob']
        assert hashlib.sha256(b).hexdigest()==row['source_sha256']
        blobchecks.append(dict(path=row['path'],git_blob_sha1=blob,sha256=row['source_sha256']))
    artifacts=[]
    for a in replay['artifacts']:
        p=GATE/'evidence/current-after-natbits'/a['path'];b=p.read_bytes()
        assert len(b)==a['bytes'] and hashlib.sha256(b).hexdigest()==a['sha256']
        artifacts.append(a['path'])
    log=(GATE/'evidence/current-after-natbits/replay-msg3.log').read_text()
    rows=[l for l in log.splitlines() if re.match(r'TCSlib/.* exit=',l)]
    assert len(rows)==329 and all('exit=0 errors=0' in l for l in rows)
    assert log.rstrip().endswith('# modules=329 failed=0')
    assert (GATE/'evidence/current-after-natbits/replay-msg3-static.txt').read_text().strip()=='modules 329, mismatches 0, static total 67'
    out=dict(dispatch=dispatch,bundle_sections=166,audit_sha256=hashlib.sha256(audit).hexdigest(),
             source_counts={f:len(ds) for f,ds in all_decl.items()},source_details=details,
             audited_current_blob_checks=blobchecks,
             msg3=dict(modules=329,failed=0,static_mismatches=0,static_admissions=67,
                       all_receipt_artifact_hashes_match=True,artifacts=artifacts),
             limitation='Hashes and supplied evidence parsed independently; no Git object read, replay, Lean, seal, screen, or payload script execution.')
    (OUT/'crosschecks.json').write_text(json.dumps(out,indent=2)+'\n')
    print('source counts',out['source_counts'])
    print('audit/bundle integrity PASS; four audited/current source blobs match; msg3 artifact hashes and329 recorded exits/static67 match')
    for f in [sat,hard]:print(f,[(d['name'],d['span_lines']) for d in details[f]])


if __name__=='__main__':main()
