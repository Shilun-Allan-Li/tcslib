"""Population drift between the round-1 screen copies (received tree) and the campaign tip.
For each file of the round-1 labels (flat label, repository path, SHA-256 at the received tree):
IDENTICAL if the tip file has the recorded SHA-256; otherwise CODE-IDENTICAL if the screen's
comment strip of both versions is equal (so every screen result is unchanged; only line numbers
may move), else CODE-CHANGED.
usage: python3 -I popdrift.py <labels.tsv> <round1-screen-root> <checkout-root>"""
import sys, hashlib, os
labels, sroot, root = sys.argv[1:4]
def strip(src):
    out = []; i = 0; depth = 0; n = len(src)
    while i < n:
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        out.append(src[i]); i += 1
    return ''.join(out)
cnt = {}
for l in open(labels, encoding='utf-8'):
    flat, path, sha = l.rstrip('\n').split('\t')
    old = open(os.path.join(sroot, flat), 'rb').read()
    assert hashlib.sha256(old).hexdigest() == sha, flat
    p = os.path.join(root, path)
    if not os.path.exists(p): k = 'MISSING-AT-TIP'
    else:
        new = open(p, 'rb').read()
        if new == old: k = 'IDENTICAL'
        elif strip(new.decode()) == strip(old.decode()): k = 'CODE-IDENTICAL'
        else: k = 'CODE-CHANGED'
    cnt[k] = cnt.get(k, 0) + 1
    if k != 'IDENTICAL': print(k, path)
print('summary:', cnt)
