import json,sys
EV='/home/user/dw10/sub/snap-r1'
decl=sys.argv[1]; var=sys.argv[2] if len(sys.argv)>2 else 'coe-A'; n=int(sys.argv[3]) if len(sys.argv)>3 else 3000
for l in open(EV+'/seal-errors.jsonl'):
    e=json.loads(l)
    if e['declaration'].endswith(decl) and (var=='all' or e['variant']==var):
        print('#### %s %s line %s probe %s casc=%s cls=%s'%(e['declaration'],e['variant'],e['source_line'],e['probe_line'],e['cascade'],e['message_class']))
        print('prov:',e['providers']); print('ref:',e['referenced'])
        print(e["message"].split("G06-COMPONENT")[0][:n])
