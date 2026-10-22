import sys, hashlib
bundle, path = sys.argv[1], sys.argv[2]
lines=open(bundle,encoding='utf-8').read().split('\n')
idx=[i for i,l in enumerate(lines) if l.startswith('## ===== ') and l.endswith(' =====')]
for k,i in enumerate(idx):
    if lines[i][9:-6]==path:
        j=idx[k+1] if k+1<len(idx) else len(lines)
        body=lines[i+1:j]
        # try common framing: optional fence lines
        txt='\n'.join(body)
        for cand in (txt, txt.rstrip('\n')+'\n', '\n'.join(body[:-1]), '\n'.join(body[:-1])+'\n', '\n'.join(body[1:-2])+'\n', '\n'.join(body[2:-2])+'\n', '\n'.join(body[1:-1])+'\n'):
            b=cand.encode()
            h=hashlib.sha1(b'blob %d\0'%len(b)+b).hexdigest()
            print(h)
        break
