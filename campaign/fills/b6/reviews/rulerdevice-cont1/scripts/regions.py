import sys, re, subprocess
# usage: regions.py <repo> <base> <head> <file> ; prints -U0 hunks and classifies against the brief's regions
repo, base, head, f = sys.argv[1:5]
d = subprocess.run(['git','-C',repo,'diff','-U0',base,head,'--',f],capture_output=True,text=True).stdout
bl = subprocess.run(['git','-C',repo,'show',f'{base}:{f}'],capture_output=True,text=True).stdout.split('\n')
H = re.compile(r'^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@')
hunks=[]; cur=None
for l in d.split('\n'):
    m=H.match(l)
    if m:
        a=int(m.group(1)); an=int(m.group(2)) if m.group(2) is not None else 1
        b=int(m.group(3)); bn=int(m.group(4)) if m.group(4) is not None else 1
        cur={'a':a,'an':an,'b':b,'bn':bn,'minus':[],'plus':[]}; hunks.append(cur); continue
    if cur is None: continue
    if l.startswith('-') and not l.startswith('---'): cur['minus'].append(l[1:])
    elif l.startswith('+') and not l.startswith('+++'): cur['plus'].append(l[1:])
for h in hunks:
    if h['an']==0:
        print(f"INSERT after base line {h['a']} ({h['bn']} lines, head {h['b']}..{h['b']+h['bn']-1}); base line {h['a']}: {bl[h['a']-1]!r}; base line {h['a']+1}: {bl[h['a']][:60]!r}")
    else:
        print(f"REPLACE base {h['a']}..{h['a']+h['an']-1} ({h['an']} lines) by {h['bn']} lines (head {h['b']}..{h['b']+h['bn']-1}); removed: {h['minus']!r}")
print('total +', sum(len(h['plus']) for h in hunks), '-', sum(len(h['minus']) for h in hunks))
