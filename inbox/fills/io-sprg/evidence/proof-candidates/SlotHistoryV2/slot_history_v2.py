#!/usr/bin/env python3
"""Tagged wrapper-history audit with ONE exact historical overlap exception.

Staged by the read-only review agent; root must archive and run. No Lean or Git.
All output is written to a fresh explicit --out directory, never old M0 host files.
This audits only tagged wrapper events, not global host processes or child lifetimes.
"""
import argparse
import datetime
import hashlib
import json
import re
import sys
from pathlib import Path

TAG = 'io-sprg'
DEFAULT_SOURCE = '/Users/seyoonr/.lean-slots/slots.log'
DEFAULT_CORRECTION = 'evidence/host/search-process-correction.json'
KNOWN_PRIOR = '93883'
KNOWN_OWNER = '93983'
KNOWN_CHILD = 93887
KNOWN_PRIOR_START = '2026-11-18T15:07:27Z'
KNOWN_OVERLAP_START = '2026-11-18T15:07:45Z'
KNOWN_OVERLAP_END = '2026-11-18T15:07:48Z'
CORRECTION_RELEASE = '2026-11-18T15:08:34Z'
KNOWN_KEYS = {
    ('ACQUIRE', KNOWN_PRIOR, KNOWN_PRIOR_START),
    ('ACQUIRE', KNOWN_OWNER, KNOWN_OVERLAP_START),
    ('RELEASE', KNOWN_OWNER, KNOWN_OVERLAP_END),
    ('RELEASE', KNOWN_PRIOR, CORRECTION_RELEASE),
}
RECORD = re.compile(r'(\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ) '
                    r'(ACQUIRE|RELEASE|REAP) pid=(\d+) tag=io-sprg (.*)')
QUALIFICATION = (
    'Audit of all extracted tag=io-sprg wrapper-event lines in one source snapshot. '
    'The known overlap violates one-wrapper-at-a-time history and is not erased. '
    'REAP closes only the observed wrapper reservation, with its provenance retained; '
    'it establishes no child end time or cause. No global host process-cap, other-job '
    'seriality, actual simultaneous Lean-process count, or complete child-process '
    'history is claimed.'
)


class AuditError(RuntimeError):
    pass


def need(condition, message):
    if not condition:
        raise AuditError(message)


def utc(stamp):
    return datetime.datetime.strptime(stamp, '%Y-%m-%dT%H:%M:%SZ').replace(
        tzinfo=datetime.timezone.utc)


def parse(line):
    match = RECORD.fullmatch(line)
    need(match is not None, 'Malformed tagged wrapper record: ' + line)
    stamp, kind, pid, rest = match.groups()
    utc(stamp)
    return stamp, kind, pid, rest


def verify_correction(correction, lines):
    need(correction.get('observed_wrapper') == int(KNOWN_PRIOR),
         'Correction prior-wrapper PID differs')
    need(correction.get('owner_wrapper') == int(KNOWN_OWNER),
         'Correction owner-wrapper PID differs')
    need(correction.get('observed_live_child') == KNOWN_CHILD,
         'Correction observed child PID differs')
    need(correction.get('confirmed_overlap_utc') ==
         [KNOWN_OVERLAP_START, KNOWN_OVERLAP_END], 'Correction overlap timestamps differ')
    saved = correction.get('slot_lines')
    need(isinstance(saved, list) and len(saved) == len(KNOWN_KEYS),
         'Correction must identify the exact four historical slot lines')
    keys = set()
    for line in saved:
        stamp, kind, pid, rest = parse(line)
        key = kind, pid, stamp
        need(key in KNOWN_KEYS and key not in keys, 'Unexpected/duplicate correction key')
        keys.add(key)
        need(lines.count(line) == 1, 'Correction line missing/duplicated in source history')
    need(keys == KNOWN_KEYS, 'Correction historical event set differs')


def audit(lines, correction):
    need(lines, 'No tagged io-sprg wrapper records')
    verify_correction(correction, lines)
    active, events, reaps, overlaps = {}, [], [], []
    markers, max_wrappers, cache3 = {}, 0, 0
    correction_seen = False
    post_count = post_max = 0
    prior_stamp = None
    for ordinal, line in enumerate(lines, 1):
        stamp, kind, pid, rest = parse(line)
        moment = utc(stamp)
        if prior_stamp is not None:
            need(moment >= prior_stamp, 'Tagged event timestamps go backwards at line ' + str(ordinal))
        prior_stamp = moment
        key = kind, pid, stamp
        if key in KNOWN_KEYS:
            need(key not in markers, 'Duplicate exact historical event')
            markers[key] = ordinal
        if correction_seen:
            need(moment >= utc(CORRECTION_RELEASE), 'Post-correction timestamp precedes cutoff')
        if kind == 'ACQUIRE':
            need(pid not in active, 'Duplicate active wrapper PID: ' + line)
            match = re.fullmatch(r'k=(\d+) cmd=(.*)', rest)
            need(match is not None, 'Malformed ACQUIRE payload: ' + line)
            k, command = int(match[1]), match[2]
            need(k in {1, 3}, 'Unexpected requested slot count: ' + line)
            if k == 3:
                need('lake exe cache get ' in command, 'k=3 is not a recorded cache-get command')
                cache3 += 1
            if active:
                exact = (
                    pid == KNOWN_OWNER and stamp == KNOWN_OVERLAP_START
                    and set(active) == {KNOWN_PRIOR}
                    and active[KNOWN_PRIOR]['start'] == KNOWN_PRIOR_START
                    and active[KNOWN_PRIOR]['k'] == k == 1
                    and not overlaps and not correction_seen
                )
                need(exact, 'UNEXPECTED OVERLAP; no exception for this PID/timestamp: '
                     + repr(active) + ' / ' + line)
                overlaps.append({
                    'prior_pid': KNOWN_PRIOR, 'owner_pid': KNOWN_OWNER,
                    'start': stamp, 'start_line': ordinal,
                    'exception': 'Exact correction-record PID/timestamp pair only',
                    'seriality_violation': True,
                })
            event = {'pid': pid, 'start': stamp, 'k': k, 'command': command,
                     'acquire_line': ordinal}
            active[pid] = event
            events.append(event)
            max_wrappers = max(max_wrappers, len(active))
            if correction_seen:
                post_count += 1
                post_max = max(post_max, len(active))
        elif kind == 'RELEASE':
            need(pid in active, 'Unmatched RELEASE: ' + line)
            if pid == KNOWN_OWNER and stamp == KNOWN_OVERLAP_END:
                need(set(active) == {KNOWN_PRIOR, KNOWN_OWNER}
                     and len(overlaps) == 1 and 'end' not in overlaps[0],
                     'Known owner release does not end the exact known active pair')
                overlaps[0].update(end=stamp, end_line=ordinal,
                                   seconds=int((moment - utc(overlaps[0]['start'])).total_seconds()))
            event = active.pop(pid)
            seconds = int((moment - utc(event['start'])).total_seconds())
            need(seconds >= 0, 'RELEASE precedes acquisition')
            event.update(end=stamp, release_line=ordinal, seconds=seconds,
                         termination='RELEASE recorded; no independent child-process end inference')
            if pid == KNOWN_PRIOR and stamp == CORRECTION_RELEASE:
                need(event['start'] == KNOWN_PRIOR_START and not active,
                     'Correction wrapper release has wrong acquisition or active peers')
                need(len(overlaps) == 1 and overlaps[0].get('end') == KNOWN_OVERLAP_END,
                     'Known overlap must end at the exact owner release timestamp')
                correction_seen = True
        elif kind == 'REAP':
            dead_match = re.search(r'(?:^| )dead=(\d+)(?: |$)', rest)
            dead = dead_match[1] if dead_match else None
            reap = {'stamp': stamp, 'reaper_pid': pid, 'payload': rest,
                    'line': ordinal, 'dead_pid': dead,
                    'matched_active_wrapper': bool(dead and dead in active)}
            if dead and dead in active:
                event = active.pop(dead)
                event.update(reaped_at=stamp, reap_line=ordinal, reaper_pid=pid,
                             reap_payload=rest, termination=(
                                 'No RELEASE recorded; wrapper PID observed dead and reaped '
                                 'before next acquisition. End time/cause and child-process '
                                 'history are not inferred.'))
                reap['acquire_line'] = event['acquire_line']
            reaps.append(reap)
    need(set(markers) == KNOWN_KEYS, 'Historical exception markers are incomplete')
    need(len(overlaps) == 1 and overlaps[0].get('end') == KNOWN_OVERLAP_END,
         'Historical exception interval differs')
    need(correction_seen, 'Exact prior-wrapper correction RELEASE is absent')
    need(max_wrappers == 2, 'Maximum tagged wrapper count differs from exact known history')
    whole_serial = not overlaps
    need(not whole_serial, 'Known violation cannot be represented as historically serial')
    post_serial = post_max <= 1 if post_count else None
    need(post_serial is not False, 'Post-correction tagged wrappers are not serial')
    return {
        'acquisitions': len(events), 'max_concurrent_job_wrappers': max_wrappers,
        'cache_k3_acquisitions': cache3, 'active': active,
        'all_logged_acquisitions_serial_after_recorded_reaps': whole_serial,
        'all_tagged_wrapper_acquisitions_serial': whole_serial,
        'known_overlap_exception': overlaps[0],
        'correction_release_utc': CORRECTION_RELEASE,
        'correction_release_line': markers['RELEASE', KNOWN_PRIOR, CORRECTION_RELEASE],
        'post_correction_serial': post_serial,
        'post_correction': {
            'cutoff_utc': CORRECTION_RELEASE, 'acquisitions': post_count,
            'max_concurrent_job_wrappers': post_max, 'serial': post_serial,
            'closed': not active,
            'qualification': 'Observed tagged wrapper events after the exact correction release; '
                             'null serial value means no later acquisitions were observed.',
        },
        'unreleased_reaped': [event for event in events if 'reaped_at' in event],
        'reap_records': reaps, 'events': events,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', default=DEFAULT_SOURCE)
    parser.add_argument('--correction', default=DEFAULT_CORRECTION)
    parser.add_argument('--out', required=True, help='Fresh output directory; old M0 host paths forbidden')
    parser.add_argument('--require-closed', action='store_true')
    args = parser.parse_args()
    source, correction_path, out = map(Path, (args.source, args.correction, args.out))
    out = out.resolve()
    old_host = Path('evidence/host').resolve()
    need(out != old_host, 'Refusing to overwrite the old evidence/host M0 directory')
    log_target, summary_target = out / 'slots-io-sprg.log', out / 'slot-summary.json'
    need(all(not target.exists() for target in (log_target, summary_target)),
         'Outputs already exist; archive them or choose a fresh --out')
    need(all(target.resolve() not in {source.resolve(), correction_path.resolve()}
             for target in (log_target, summary_target)), 'Output aliases an input')
    raw = source.read_bytes()
    # Check the event's fourth field, never command text containing another tag.
    tagged = []
    for line in raw.splitlines(keepends=True):
        fields = line.rstrip(b'\r\n').split(b' ', 4)
        if len(fields) >= 4 and fields[3] == b'tag=io-sprg':
            tagged.append(line)
    extracted = b''.join(tagged)
    lines = [line.decode('utf-8').rstrip('\r\n') for line in tagged]
    correction_bytes = correction_path.read_bytes()
    correction = json.loads(correction_bytes)
    summary = {
        'as_of': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source': str(source.resolve()), 'source_sha256': hashlib.sha256(raw).hexdigest(),
        'tag': TAG, 'lines': len(lines),
        'extracted_log_sha256': hashlib.sha256(extracted).hexdigest(),
        'source_line_bytes_preserved': True,
        'correction_record': str(correction_path.resolve()),
        'correction_record_sha256': hashlib.sha256(correction_bytes).hexdigest(),
        'correction_record_contents': correction,
        'tool_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'qualification': QUALIFICATION,
    }
    failure = None
    try:
        summary.update(audit(lines, correction))
        if args.require_closed:
            need(not summary['active'], 'Tagged wrappers remain active at snapshot end')
        summary['status'] = 'PASS_WITH_EXACT_RECORDED_HISTORICAL_VIOLATION'
    except (AuditError, ValueError) as error:
        failure = str(error)
        summary.update(status='FAIL', validation_error=failure)
    out.mkdir(parents=True, exist_ok=True)
    # Exclusive creation also prevents a concurrent invocation from overwriting evidence.
    with log_target.open('xb') as handle:
        handle.write(extracted)
    with summary_target.open('x') as handle:
        handle.write(json.dumps(summary, indent=2) + '\n')
    if failure:
        print('SLOT_HISTORY_V2_FAIL', failure, file=sys.stderr)
        return 1
    print('SLOT_HISTORY_V2_KNOWN_VIOLATION', summary['acquisitions'],
          'max_tagged_wrappers', summary['max_concurrent_job_wrappers'],
          'whole_history_serial', summary['all_tagged_wrapper_acquisitions_serial'],
          'post_correction_serial', summary['post_correction_serial'],
          'active', len(summary['active']))
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (AuditError, OSError, UnicodeError, json.JSONDecodeError) as error:
        print('SLOT_HISTORY_V2_FAIL', error, file=sys.stderr)
        raise SystemExit(1)
