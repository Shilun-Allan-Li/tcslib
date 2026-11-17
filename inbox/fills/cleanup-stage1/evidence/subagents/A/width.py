import sys
for p in sys.argv[1:]:
    for i,l in enumerate(open(p,encoding='utf-8').read().split('\n'),1):
        if len(l)>100: print(p,i,len(l))
