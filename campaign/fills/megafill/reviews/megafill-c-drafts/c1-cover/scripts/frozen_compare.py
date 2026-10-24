import sys, subprocess
draft, src_rev, src_path, d_from, d_to, s_from, s_to = sys.argv[1:8]
dl = open(draft, encoding='utf-8').read().split('\n')
sl = subprocess.run(['git','show',f'{src_rev}:{src_path}'],capture_output=True,text=True,check=True).stdout.split('\n')
a = dl[int(d_from)-1:int(d_to)]
b = sl[int(s_from)-1:int(s_to)]
print('draft lines', d_from, d_to, 'n=', len(a)); print('source lines', s_from, s_to, 'n=', len(b))
print('IDENTICAL' if a == b else 'DIFFERENT')
for i,(x,y) in enumerate(zip(a,b)):
    if x != y: print('diff at', i, repr(x), repr(y))
