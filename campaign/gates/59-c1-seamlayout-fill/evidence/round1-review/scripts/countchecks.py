import re, sys
for p in sys.argv[1:]:
    src=open(p).read()
    # strip block comments and line comments
    s=re.sub(r'/-.*?-/', '', src, flags=re.S)
    s=re.sub(r'--[^\n]*', '', s)
    names=re.findall(r'^\s*#check\s+@?([^\s()]+)', s, flags=re.M)
    print(f"{p.split('/')[-1]}: #check commands {len(names)}; distinct names {len(set(names))}")
    if len(sys.argv)>2: pass
