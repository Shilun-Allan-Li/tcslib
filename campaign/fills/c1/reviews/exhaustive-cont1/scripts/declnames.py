"""Declaration names of a Lean file (declfreeze's chunker), namespace-qualified by `Turing.`.
usage: python3 -I declnames.py <declfreeze.py> <file>  -> prints 'private|public <name>'"""
import importlib.util, sys
spec = importlib.util.spec_from_file_location('df', sys.argv[1])
src = open(sys.argv[1], encoding='utf-8').read()
# load only the function definitions of declfreeze (it runs its comparison at import time)
code = src.split('\na = chunks(')[0]
ns = {}
exec(compile(code, sys.argv[1], 'exec'), ns)
for n, p, t in ns['chunks'](open(sys.argv[2], encoding='utf-8').read()):
    print(('private ' if p else 'public ') + 'Turing.' + n)
