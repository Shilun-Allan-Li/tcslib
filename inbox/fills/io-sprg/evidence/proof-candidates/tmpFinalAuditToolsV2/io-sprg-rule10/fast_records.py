"""io-sprg Mac Rule10 transport adaptation, 2026-11-18; no Lean invocation.

Apply AFTER the reviewed request adapter and optional CHUNK wrapper.  Only G06
success-record emission changes: MessageData is rendered directly to stdout
instead of being retained in Lean's diagnostic MessageLog.  All requests,
identity checks, local irreducible attributes, unfolding masks, exact full
lookup-state comparisons, counts, errors, and EOF checks remain byte-identical.
The replacement preserves line counts and therefore source-to-probe line maps.
Host root: /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange.
"""
import re

HEADER_NOTE = ' /- io-sprg: success transport=IO.println/MessageData.toString; guards unchanged -/'
TAGS = ('G06-COMPONENT ', 'G06-NAME ', 'G06-MASK ', 'G06-SEAL ',
        'G06-SEAL-END ', 'G06-CONTROL-CATALOG ')
LINE = re.compile(r'^(\s*)Lean\.logInfo (m!"(?:[^"\\]|\\.)*")$')


def rewrite(raw: bytes) -> bytes:
    """Return line-preserving output and reject unexpected G06 logging syntax."""
    text = raw.decode('utf-8')
    result = []
    changed = 0
    for original in text.splitlines(keepends=True):
        ending = '\n' if original.endswith('\n') else ''
        body = original[:-1] if ending else original
        if any('Lean.logInfo m!"' + tag in body for tag in TAGS):
            m = LINE.fullmatch(body)
            if not m:
                raise RuntimeError('unexpected G06 success-record line: ' + body[:160])
            body = m[1] + 'IO.println (← (' + m[2] + ').toString)'
            changed += 1
        if body.startswith('/- G06-HARNESS ') or body.startswith('/- G06-CONTROL-CATALOG '):
            body += HEADER_NOTE
        result.append(body + ending)
    if not changed:
        raise RuntimeError('no supported G06 success records found')
    output = ''.join(result).encode('utf-8')
    if output.count(b'\n') != raw.count(b'\n'):
        raise RuntimeError('G06 transport changed line count')
    # A reversible textual normalization proves all non-emission source bytes equal.
    restored = output.decode('utf-8').replace(HEADER_NOTE, '')
    restored = re.sub(r'^(\s*)IO\.println \(← \((m!"(?:[^"\\]|\\.)*")\)\.toString\)$',
                      lambda m: m[1] + 'Lean.logInfo ' + m[2], restored, flags=re.M)
    if restored.encode('utf-8') != raw:
        raise RuntimeError('G06 transport altered non-emission source bytes')
    return output


def configure_builders(bs, controls=None):
    """Decorate already configured builders; do not edit the reviewed adapters."""
    if getattr(bs, 'iosprg_fast_records_configured', False):
        raise RuntimeError('io-sprg success transport configured twice')
    original = bs.seal_command
    bs.seal_command = lambda label, rows, *, end: rewrite(original(label, rows, end=end))
    if controls is not None:
        catalog = controls.catalog_command
        controls.catalog_command = lambda builder, label, rows, phase: rewrite(
            catalog(builder, label, rows, phase))
    bs.iosprg_fast_records_configured = True
