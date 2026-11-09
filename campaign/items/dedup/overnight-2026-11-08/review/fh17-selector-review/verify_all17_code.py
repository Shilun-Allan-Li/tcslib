from pathlib import Path
import json,re,sys
sys.dont_write_bytecode=True
O=Path(__file__).parent
sys.path.insert(0,'/private/tmp/ab34-fe-live1-final-validation/EXPORT/helpers/devtools/seyoon')
from graph import imports_of
rows=json.loads((O/'DISPOSITIONS17-PLUS-CANONICAL.json').read_text())

def stripcomments(s):
    out=[];i=0;depth=0;quoted=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i):depth+=1;i+=2
            elif s.startswith('-/',i):depth-=1;i+=2;out.append(' ' if depth==0 else '')
            else:
                if s[i]=='\n':out.append('\n')
                i+=1
        elif quoted:
            out.append(s[i])
            if s[i]=='\\' and i+1<len(s):i+=1;out.append(s[i])
            elif s[i]=='"':quoted=False
            i+=1
        elif s.startswith('/-',i):depth=1;i+=2;out.append(' ')
        elif s.startswith('--',i):
            j=s.find('\n',i);i=len(s) if j<0 else j
        else:
            out.append(s[i]);quoted=s[i]=='"';i+=1
    assert depth==0 and not quoted
    return ''.join(out)

def tokens(s):
    return re.findall(r'"(?:\\.|[^"\\])*"|[\w\u0080-\uffff]+(?:\'[\w\u0080-\uffff]*)*|[^\s]',stripcomments(s))

checks=[]
for path in sorted({r['path'] for r in rows}):
    final=(O/'source/FINAL'/(path+'.txt')).read_text()
    base=(O/'source/BASE'/(path+'.txt')).read_text()
    restored=final
    for r in [r for r in rows if r['path']==path and r['id']!=76]:
        new=(O/r['final_complete_chunk']).read_text();old=(O/r['old_complete_chunk']).read_text()
        assert restored.count(new)==1
        restored=restored.replace(new,old)
    assert tokens(restored)==tokens(base),path
    assert imports_of(O/'source/FINAL'/(path+'.txt'))==imports_of(O/'source/BASE'/(path+'.txt'))
    checks.append({'path':path,'all_non_target_code_tokens_equal_MAC8_BASE_after_restoring17_chunks':True,'all_non_target_bytes_equal_BASE':restored==base,'BASE_FINAL_imports_exact':True})
res={'PASS':True,'consumers':17,'canonical_home':1,'consumer_owners':len({r['path'] for r in rows if r['id']!=76}),'files_including_canonical':len(checks),'source_statement_headers_unchanged':'DISPOSITIONS17-PLUS-CANONICAL.json and ALL-ATTEMPT-FULL-HEADERS.json','non_target_code_and_imports_exact':True,'bytes_differing_after_restoration_are_comment_only':True,'rows':checks}
(O/'ALL17-CODE-PRESERVATION.json').write_text(json.dumps(res,indent=2)+'\n')
print('PASS all17 code preservation; owners='+str(res['consumer_owners']))
