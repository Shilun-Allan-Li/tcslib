import sys, re, subprocess
# usage: regions.py <repo> <base> <head> <path>
repo, base, head, path = sys.argv[1:5]
def show(rev): return subprocess.run(['git','-C',repo,'show',f'{rev}:{path}'],capture_output=True,text=True,check=True).stdout.split('\n')
A, B = show(base), show(head)
d = subprocess.run(['git','-C',repo,'diff','-U0',base,head,'--',path],capture_output=True,text=True,check=True).stdout
hunks = []
for m in re.finditer(r'^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@', d, re.M):
    a0, an, b0, bn = int(m[1]), int(m[2] or 1), int(m[3]), int(m[4] or 1)
    hunks.append((a0, an, b0, bn))
print('hunks (base start,count -> head start,count):', hunks)
# expected regions at base line numbers
exp = {11: 'import region (a): insert after base line 11', 1688: 'region (b): insert after blank 1688',
       1725: 'region (d): U2-U body sorry', 1728: 'region (c): insert after blank 1728', 1760: 'region (d): U2-E body sorry'}
ok = True
for a0, an, b0, bn in hunks:
    removed = A[a0-1:a0-1+an] if an else []
    added = B[b0-1:b0-1+bn]
    key = a0
    desc = exp.get(key, 'UNEXPECTED')
    if desc == 'UNEXPECTED': ok = False
    print(f'- base {a0},{an}: {desc}; removed {removed!r}; added {len(added)} lines')
    if an == 0:
        print(f'    context: base[{a0}]={A[a0-1]!r}, base[{a0+1}]={A[a0] if a0 < len(A) else None!r}')
    if desc.startswith('region (d)') and removed != ['  sorry']: ok = False; print('    REMOVED NOT A SORRY')
    if key == 11 and added != ['import TCSlib.Complexity.TuringMachine.Build.Rewind']: ok = False; print('    IMPORT MISMATCH')
print('all hunks in regions:', ok)
# header/status lines 29-32 and the startup section identical
for lo, hi, name in [(1, 11, 'imports before overlay'), (12, 1688, 'module header .. startup section .. U2-U section header + blank'), (1689, 1724, 'U2-U docstring + statement'), (1726, 1728, 'U2-U end .. U2-E header + blank'), (1729, 1759, 'U2-E docstring + statement'), (1761, len(A), 'tail')]:
    # map base line -> head line via hunks
    def mp(l):
        off = 0
        for a0, an, b0, bn in hunks:
            if an == 0:
                if l > a0: off += bn
            else:
                if l >= a0 + an: off += bn - an
        return l + off
    seg_a = A[lo-1:hi]; seg_b = B[mp(lo)-1:mp(lo)-1+len(seg_a)]
    print(f'base {lo}-{hi} == head {mp(lo)}-{mp(lo)+len(seg_a)-1} ({name}):', seg_a == seg_b)
print('status lines base 29-32:'); [print('   ', A[i-1]) for i in range(29, 33)]
