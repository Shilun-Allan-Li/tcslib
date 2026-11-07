import sys, re, os, hashlib
bundle, root, lst = sys.argv[1], sys.argv[2], sys.argv[3]
raw = open(bundle,'rb').read()
print('sha256', hashlib.sha256(raw).hexdigest(), 'bytes', len(raw))
b = raw.decode('utf-8')
hdr = re.compile(r'^## ===== (.+?) =====\n\n', re.M)
ms = list(hdr.finditer(b))
paths = [l.strip() for l in open(lst) if l.strip()]
names=[m.group(1) for m in ms]
print('segments', len(ms), 'list', len(paths), 'order-equal', names==paths)
bad=0
for i,m in enumerate(ms):
    end = ms[i+1].start()-1 if i+1 < len(ms) else len(b)
    c = b[m.end():end]
    p = m.group(1)
    if p.endswith('.lean') or p.endswith('.py'):
        if not (c.startswith('```\n') and c.endswith('```\n')): print('FENCE?',p); bad+=1; continue
        c = c[4:-4]
    if '..' in p.split('/') or p.startswith('/'): print('UNSAFE',p); bad+=1; continue
    out = os.path.join(root,p); os.makedirs(os.path.dirname(out) or '.', exist_ok=True)
    open(out,'w',encoding='utf-8',newline='').write(c)
print('problems', bad)
