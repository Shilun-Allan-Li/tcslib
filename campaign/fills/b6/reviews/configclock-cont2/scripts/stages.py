import os, re, sys
# usage: stages.py <worktree> <order list> <stage1 log> <stage2 log> : stage 1 = the order list's modules upstream
# of WindowClock (and WindowClock) in list order; stage 2 = the rest in list order.
root, order_p, s1, s2 = sys.argv[1:5]
order = [l.strip() for l in open(order_p, encoding='utf-8') if l.strip()]
def imps(m):
    p = os.path.join(root, m + '.lean')
    return [x.replace('.', '/') for x in re.findall(r'^import\s+(TCSlib\S*)', open(p, encoding='utf-8').read(), re.M)]
up, todo = set(), ['TCSlib/Complexity/SpaceComplexity/WindowClock']
while todo:
    m = todo.pop()
    for i in imps(m):
        if i not in up: up.add(i); todo.append(i)
def mods(p): return [m.group(1) for m in re.finditer(r'^=== (\S+) start', open(p, encoding='utf-8', errors='replace').read(), re.M)]
a, b = mods(s1), mods(s2)
exp1 = [m for m in order if m in up or m == 'TCSlib/Complexity/SpaceComplexity/WindowClock']
exp1b = [m for m in order if m in up]
print('WindowClock upstream TCSlib modules:', len(up), '; of them in the order list:', len(exp1b))
print('stage 1:', len(a), 'modules; == upstream in list order:', a == exp1b, '; == upstream + WindowClock in list order:', a == exp1)
print('stage 2:', len(b), 'modules; == the rest in list order:', b == [m for m in order if m not in a])
print('stage 1 + stage 2 == order list as a set:', sorted(a + b) == sorted(order), '; duplicates:', len(a + b) - len(set(a + b)))
print('WindowClock in stage:', 1 if 'TCSlib/Complexity/SpaceComplexity/WindowClock' in a else 2 if 'TCSlib/Complexity/SpaceComplexity/WindowClock' in b else None)
