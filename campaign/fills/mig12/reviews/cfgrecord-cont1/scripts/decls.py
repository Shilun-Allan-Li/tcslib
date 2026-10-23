import sys
# usage: decls.py <declfreeze.py> <file>: every declaration (name, private?, kind) by declfreeze's parser
src = open(sys.argv[1], encoding='utf-8').read()
src = src[:src.index('a = chunks(open(sys.argv[1]')]
ns = {}; exec(compile(src, sys.argv[1], 'exec'), ns)
for n, p, t in ns['chunks'](open(sys.argv[2], encoding='utf-8').read()):
    body = t.split('-/', 1)[1] if t.startswith('/--') else t
    m = ns['DECL'].match(body.strip().split('\n')[0]) or ns['DECL'].match(body.lstrip())
    print(n, 'private' if p else 'public', m.group(4) if m else '?')
