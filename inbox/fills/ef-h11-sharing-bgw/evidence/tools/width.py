import sys
for f in sys.argv[1:]:
    L=open(f,encoding='utf-8').read().split('\n')
    bad=[(i+1,len(l)) for i,l in enumerate(L) if len(l)>100]
    print(f, 'lines', len(L)-1 if L[-1]=='' else len(L), 'maxwidth', max(len(l) for l in L), 'over100', bad)
