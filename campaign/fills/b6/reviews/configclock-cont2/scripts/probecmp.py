import difflib, sys
# usage: probecmp.py <delivered module> <probe copy> : lines of the probe copy not in the module (and vice versa)
a = open(sys.argv[1], encoding='utf-8').read().split('\n'); b = open(sys.argv[2], encoding='utf-8').read().split('\n')
add = rem = 0
for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
    if tag == 'equal': continue
    rem += i2 - i1; add += j2 - j1
    if i2 > i1: print(f'  module lines {i1+1}-{i2} not in the copy:', a[i1:i2][:3])
    print(f'  copy lines {j1+1}-{j2} added ({j2-j1}):', [l[:90] for l in b[j1:j2][:4]], '...' if j2 - j1 > 4 else '')
print(f'module lines missing from the copy: {rem}; lines added in the copy: {add}')
