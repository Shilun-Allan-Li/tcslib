import json,sys
last={}
for l in open('/workspace/cp2/evidence/logs/checks-dev.jsonl'):
    r=json.loads(l); last[r['module']]=r
for i,m in enumerate([l.strip() for l in open(sys.argv[1]) if l.strip()],1):
    r=last.get(m)
    print(i, (r or {}).get('status','-'), m, (r or {}).get('parsed_errors',''))
