"""Own read-only follow-up: original CP1 failed-attempt raw diagnostic coverage."""
from pathlib import Path
import collections
import hashlib
import json
import re

OUT=Path(__file__).resolve().parent
P=OUT.parent/'payload'
EV=P/'evidence/logs'
source=EV/'checks-dev.jsonl'
rows=[json.loads(line) for line in source.read_text().splitlines() if line]
fails=[(number,row) for number,row in enumerate(rows,1) if row['status']=='FAIL']
logs={str(f.relative_to(P)):f.read_text(errors='strict') for f in P.rglob('*.log') if f.is_file()}
inventory=[{'path':name,'bytes':len(text.encode()),'sha256':hashlib.sha256(text.encode()).hexdigest()}
           for name,text in sorted(logs.items())]
diag=re.compile(r'(?m)^([^\n]+?\.lean):(\d+):(\d+): error[^:]*: ?([^\n]*)')
ordinary_prefix='/workspace/cp2/src/'
by_source=collections.defaultdict(list)
global_diagnostics=[]
for path,text in logs.items():
    for match in diag.finditer(text):
        filename=match[1].removeprefix(ordinary_prefix)
        by_source[filename].append({'log':path,'log_line':text.count('\n',0,match.start())+1,
            'source_file':filename,'source_line':int(match[2]),'source_column':int(match[3]),'message':match[4]})
    for match in re.finditer(r'(?m)^error: ?([^\n]*)',text):
        global_diagnostics.append({'log':path,'line':text.count('\n',0,match.start())+1,'text':match[0]})
attempts=[]
for number,row in fails:
    exact=[];start_hits=[];sha_hits=[];summaries=[]
    expected_summary=(f"FAIL {row['module']} rc={row['rc']} errors={row['parsed_errors']} "
        f"fresh={row['object_fresh_nonempty']} {row['elapsed_s']}s {row['maxrss_kib']//1024}MiB")
    for path,text in logs.items():
        if row['start'] in text:
            start_hits.append(path)
            if row['source_sha256'] in text:
                locations=[m for m in diag.finditer(text) if m[1].removeprefix(ordinary_prefix)==row['module']+'.lean']
                exact.append({'log':path,'source_start_match':True,'source_sha_match':True,'original_source_diagnostics':len(locations)})
        if row['source_sha256'] in text:sha_hits.append(path)
        for i,line in enumerate(text.splitlines(),1):
            if line==expected_summary:summaries.append({'log':path,'line':i,'text':line})
    referenced='evidence/logs/'+row['log'].split('/evidence/logs/',1)[1]
    current=logs[referenced]
    current_start=re.search(r'^START (.+)$',current,re.M)
    attempts.append({'checks_dev_row':number,'module':row['module'],'source':row['source'],
        'source_sha256':row['source_sha256'],'start':row['start'],'end':row['end'],'pid':row['pid'],
        'rc':row['rc'],'parsed_errors_reported':row['parsed_errors'],'recorded_log':referenced,
        'current_log_start':current_start[1] if current_start else None,
        'exact_attempt_logs':exact,'start_timestamp_hits':start_hits,'source_sha_hits':sha_hits,
        'original_module_raw_diagnostics_any_log':by_source.get(row['module']+'.lean',[]),
        'matching_console_summary_lines':summaries,
        'coverage':'raw-diagnostics-found' if any(r['original_source_diagnostics'] for r in exact) else
                   'summary-only' if summaries else 'metadata-only'})
result={'delivery_commit':'8b133945c3ba4aa7abb3b896bec38441535959b2',
    'frozen_review_record_commit_from_root':'388f89436a0b1f216a4970d665c3cedbcb152e47',
    'frozen_review_md_sha256':hashlib.sha256((OUT/'report.md').read_bytes()).hexdigest(),
    'independent_followup_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'checks_dev_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
    'raw_log_files_examined':len(logs),'raw_log_bytes_examined':sum(i['bytes'] for i in inventory),
    'raw_log_inventory_sha256':hashlib.sha256(json.dumps(inventory,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
    'failed_records':len(attempts),'coverage_counts':dict(collections.Counter(a['coverage'] for a in attempts)),
    'exact_attempt_log_matches':sum(bool(a['exact_attempt_logs']) for a in attempts),
    'original_module_diagnostic_matches':sum(bool(a['original_module_raw_diagnostics_any_log']) for a in attempts),
    'global_unlocated_error_lines':global_diagnostics,'attempts':attempts,
    'limits':['Search is limited to the immutable delivered CP1 payload, not the worker filesystem/session/backups',
        'Console FAIL summaries preserve error counts only, not native Lean message bodies',
        'No claim that originals cannot later be supplied in a separately pinned supplement',
        'No incoming program executed/imported; no native/source/Git mutation']}
(OUT/'failure-log-addendum.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('attempts','global_unlocated_error_lines')},indent=2))
print('global unlocated error lines',len(global_diagnostics))
