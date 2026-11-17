import json,sys
r=json.load(open('/home/user/dw10/sub/snap-r1/readers/readers-v4.json'))
old=json.load(open('/home/user/dw10/sub/snap-r1/readers/readers.json'))
for q in sys.argv[1:]:
    hits=[k for k in r if k==q or k.endswith('.'+q)]
    if not hits: print(q,'-> NONE')
    for k in hits:
        new=[x[0] for x in r[k] if x not in old.get(k,[])]
        print(k,'->',[x[0].split('.')[-1]+'@'+x[1].split('.')[-1] for x in r[k]],'| NEW:',new)
