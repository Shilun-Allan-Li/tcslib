import re,sys
order=[l.strip() for l in open(sys.argv[1]) if l.strip()]
pos={m:i for i,m in enumerate(order)}
bad=0
for m in order:
    for l in open(m+'.lean'):
        mm=re.match(r'^import\s+(TCSlib\S*)',l)
        if mm:
            d=mm.group(1).replace('.','/')
            if d not in pos: print("NOT IN ORDER",m,"<-",d); bad+=1
            elif pos[d]>pos[m]: print("OUT OF ORDER",m,"<-",d); bad+=1
print("topological check:", "PASS" if bad==0 else f"FAIL {bad}")
