"""Summarize seal results.jsonl files (python3 -I). Usage: rule10_summary.py <dir> [<dir> ...]
One line per probe: phase, file, variant, sealed definitions, errors (error: / error( ), failing
declarations by source line, harness validity, max RSS."""
import json, sys
from pathlib import Path
for d in sys.argv[1:]:
    for line in (Path(d) / 'results.jsonl').read_text().splitlines():
        r = json.loads(line)
        lines = sorted({e['source_line'] for e in r['errors']})
        print(f'{Path(d).name:<9} {Path(r["source"]).name if "source" in r else r.get("control")} '
              f'{r.get("mode", "")}_{"coe" if r.get("coe") else "strict"} sealed={r.get("requests")} '
              f'errors={r["error_count"]} (error:={r["error_colon"]}, error(={r["error_paren"]}) '
              f'failing_source_lines={lines} harness={r.get("harness_valid")} '
              f'maxrss_kib={r.get("max_rss_kib")}')
