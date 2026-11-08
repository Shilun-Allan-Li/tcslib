from pathlib import Path
import json,hashlib
O=Path(__file__).parent;pin=json.loads((O/'PIN.json').read_text());P=O/'live/collector-project';suffix=(O/'CollectorSuffix.lean.txt').read_text();rows=[]
for source in pin['source_files']:
 path=source['path'];wanted=[r['name'] for r in pin['roots'] if r['path']==path];text=(O/'source'/(path+'.txt')).read_text()+suffix.replace('__TARGET_SUFFIXES__',json.dumps(wanted,ensure_ascii=False));f=P/path;f.write_text(text);d=O/'collector-inputs'/(path+'.txt');d.parent.mkdir(parents=True,exist_ok=True);d.write_text(text);rows.append({'path':path,'targets':wanted,'original_source_sha256':source['sha256'],'full_input_sha256':hashlib.sha256(text.encode()).hexdigest(),'input_evidence':str(d.relative_to(O))})
(O/'COLLECTOR-INPUTS.json').write_text(json.dumps(rows,indent=2)+'\n');print('Collector inputs ready',len(rows))
