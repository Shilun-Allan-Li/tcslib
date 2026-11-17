import csv, json, sys, collections
EV='/home/user/dw10/sub/snap-r1'
rows=[r for r in csv.DictReader(open(EV+'/review/open-items.tsv'),delimiter='\t') if r['agent']=='sub-B']
errs=collections.defaultdict(list)
for l in open(EV+'/seal-errors.jsonl'):
    e=json.loads(l); errs[(e['path'],e['declaration'])].append(e)
json.dump(rows,open('rows.json','w'))
filt=sys.argv[1] if len(sys.argv)>1 else ''
full=len(sys.argv)>2
for r in rows:
    if filt not in r['base_path']: continue
    print('='*100)
    print(r['key'],r['channel'],r['declaration'],'sA',r['strict_A'],'sB',r['strict_B'],'cA',r['coe_A'],'cB',r['coe_B'],'scan',r['scan'],r['status'])
    print('  class:',r['class'],'| stmt:',r['statement_level'],'| fix:',r['fix'])
    print('  record:',r['record'],'| known:',r['known_record'],'| ev:',r['evidence'])
    es=errs.get((r['base_path'],r['declaration']),[])
    for v in ['coe-A','strict-A','coe-B','strict-B']:
        ve=[e for e in es if e['variant']==v]
        for i,e in enumerate(ve):
            if i>= (3 if full else 1): break
            print('  [%s] line %s casc=%s cls=%s prov=%s'%(v,e['source_line'],e['cascade'],e['message_class'],','.join(e['providers'])))
            m=e['message']
            print('    '+m[:(1500 if full else 400)].replace('\n','\n    '))
