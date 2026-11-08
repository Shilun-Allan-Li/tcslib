"""Bound routing inputs without dropping document blocks or catalog entries."""
from __future__ import annotations

import hashlib
from collections import Counter, deque
from concurrent.futures import CancelledError
from copy import deepcopy
import json
from pathlib import Path
import tempfile
from collections.abc import Mapping, Sequence

from proofmatch.artifacts import atomic_json as _atomic_json
from proofmatch.agents import Agent, AgentInvocationError, AgentOutputError, validate_against_schema

# Measured with the same pretty-printed JSON used by Agent._envelope. Leave
# ample room below Codex's 1,048,576-character limit for prompts and CLI context.
MAX_ROUTING_CHARS = 360_000


def payload_chars(value) -> int:
    return len(json.dumps(value, ensure_ascii=False, indent=2))


def _partition(rows, make_payload, limit, max_rows):
    chunk = []
    for row in rows:
        candidate = chunk + [row]
        if chunk and (len(candidate) > max_rows or payload_chars(make_payload(candidate)) > limit):
            yield chunk
            chunk = []
        chunk.append(row)
        if payload_chars(make_payload(chunk)) > limit:
            raise ValueError('A single routing item exceeds the request budget')
    if chunk:
        yield chunk


def routing_payloads(profile: Mapping, rows: Sequence[dict], row_key: str, *,
                     extra: Mapping | None = None, max_rows: int = 120,
                     max_chars: int = MAX_ROUTING_CHARS):
    """Offer every (document block, catalog row) pair in a bounded request.

    Long profiles are split in document order; each segment is offered to all
    rows. Global headings are retained for context. No lexical filter or cap
    discards a block, row, or selected chapter.
    """
    if not rows:
        return
    base = {key: value for key, value in profile.items() if key != 'blocks'}
    blocks = profile.get('blocks', [])
    parts = list(_partition(blocks, lambda chunk: {**base, 'blocks': chunk},
                            max_chars // 2 - 1024, max(len(blocks), 1))) or [[]]
    for number, part in enumerate(parts, 1):
        document = {**base, 'blocks': part}
        if len(parts) > 1:
            document.update(document_part=number, document_parts=len(parts))
        def make_payload(chunk):
            return {'document': document, **(extra or {}), row_key: chunk}
        for chunk in _partition(rows, make_payload, max_chars, max_rows):
            yield make_payload(chunk)


MAX_RECOVERY_CALLS = 12
SINGLE_ENTRY_ATTEMPTS = 2


def _invoke_route(agent, prompt, payload, row_key, id_key, item_schema, prompt_text):
    if not isinstance(agent, Agent):
        return agent.run(prompt, payload)
    # Required object properties prevent missing/repeated identifiers. A shared
    # definition keeps the schema small even for hundreds of allowed block IDs.
    decision = deepcopy(item_schema)
    decision['properties'].pop(id_key)
    decision['required'] = [key for key in decision['required'] if key != id_key]
    if row_key == 'declarations':
        blocks = [block['block_id'] for block in payload['document']['blocks']]
        # Bound dynamic enum size; local validation always checks every block.
        if blocks and len(blocks) <= 900 and sum(map(len, blocks)) <= 14_000:
            decision['properties']['document_blocks']['items']['enum'] = blocks
    names = [row[id_key] for row in payload[row_key]]
    schema = {
        'type': 'object', 'additionalProperties': False, 'required': ['decisions'],
        'properties': {'decisions': {
            'type': 'object', 'additionalProperties': False, 'required': names,
            'properties': {name: {'$ref': '#/$defs/decision'} for name in names}}},
        '$defs': {'decision': decision},
    }
    instructions = (prompt_text + '\n\nResponse transport for this request: replace the earlier array '
                    'format with an object containing "decisions". Its keys must be exactly the '
                    f'supplied {id_key} values. Each value contains the decision fields, omitting '
                    f'{id_key} because it is already the key. Return every supplied key, including '
                    'negative decisions. Cite only exact block_id values in document.blocks. '
                    'Do not infer or manufacture identifiers.\n')
    with tempfile.TemporaryDirectory(prefix='proofmatch-routing-') as tmp:
        root = Path(tmp)
        (root / 'prompts').mkdir(); (root / 'schemas').mkdir()
        (root / 'prompts/route.md').write_text(instructions)
        (root / 'schemas/route.json').write_text(json.dumps(schema))
        worker = Agent(root, runner=agent.runner, model=agent.model, backend=agent.backend)
        answer = worker.run('route', payload)
        agent.spent_usd += worker.spent_usd
    decisions = answer.get('decisions')
    if not isinstance(decisions, dict) or set(decisions) != set(names):
        raise AgentOutputError('Routing response does not contain the exact required keys')
    if any(not isinstance(value, dict) for value in decisions.values()):
        raise AgentOutputError('Routing decisions must be objects')
    return {row_key: [{**decisions[name], id_key: name} for name in names]}


def _valid_rows(output, payload, schema, row_key, id_key):
    expected = [row[id_key] for row in payload[row_key]]
    if not isinstance(output, dict) or set(output) != {row_key} or not isinstance(output[row_key], list):
        raise AgentOutputError(f'{row_key}: malformed routing answer')
    rows = [row for row in output[row_key] if isinstance(row, dict)]
    counts = Counter(row.get(id_key) for row in rows if isinstance(row.get(id_key), str))
    accepted, errors = {}, {}
    item_schema = schema['properties'][row_key]['items']
    blocks = {block['block_id'] for block in payload['document']['blocks']}
    for row in rows:
        name = row.get(id_key)
        if not isinstance(name, str) or name not in expected:
            continue  # Unrequested names are never associated with a real entry.
        if counts[name] != 1:
            errors[name] = 'Repeated identifier'
            continue
        try:
            validate_against_schema(row, item_schema)
            if row_key == 'declarations':
                if set(row['document_blocks']) - blocks:
                    raise AgentOutputError('Cited a block outside this document segment')
                if row['tier'] in {'proves', 'states'} and not row['document_blocks']:
                    raise AgentOutputError('A positive decision needs a supplied evidence block')
            accepted[name] = row
        except AgentOutputError as error:
            errors[name] = str(error)
    for name in expected:
        if name not in accepted:
            errors.setdefault(name, 'Missing decision')
    return accepted, errors


def cached_route(agent, prompt: str, payload: dict, budget, estimate, *,
                 model: str, cache_dir: Path | None, row_key: str, id_key: str, stop_event=None):
    """Reuse complete batches; preserve valid rows and narrowly retry bad ones.

    The original cache key is retained so existing validated work remains usable.
    A partial checkpoint is not a negative decision and is never published as a
    complete answer. Persistent invalid answers stop after a bounded retry budget.
    """
    resources = getattr(agent, 'resource_root', Path(__file__).parent)
    schema_text = (resources / 'schemas' / f'{prompt}.json').read_text()
    prompt_text = (resources / 'prompts' / f'{prompt}.md').read_text()
    schema = json.loads(schema_text)
    material = json.dumps({'model': model, 'backend': getattr(agent, 'backend', ''),
                           'prompt': prompt_text, 'schema': schema_text,
                           'payload': payload}, ensure_ascii=False, sort_keys=True)
    key = hashlib.sha256(material.encode()).hexdigest()
    cache = cache_dir / f'{prompt}-{key}.json' if cache_dir is not None else None
    progress = cache.with_suffix('.partial.json') if cache is not None else None
    expected = [row[id_key] for row in payload[row_key]]
    if len(set(expected)) != len(expected):
        raise ValueError('The routing request itself contains duplicate identifiers')
    accepted = {}
    if cache is not None and cache.is_file():
        output = json.loads(cache.read_text())
        accepted, errors = _valid_rows(output, payload, schema, row_key, id_key)
        if not errors:
            print(f'  {prompt}: {len(expected)} entries (cached)', flush=True)
            return output
    if progress is not None and progress.is_file():
        saved = json.loads(progress.read_text())
        valid, _ = _valid_rows({row_key: saved['rows']}, payload, schema, row_key, id_key)
        accepted.update(valid)
    by_id = {row[id_key]: row for row in payload[row_key]}
    pending = deque([[name for name in expected if name not in accepted]])
    calls = 0
    single_attempts = Counter()
    last_errors = {}
    while pending and calls < MAX_RECOVERY_CALLS:
        if stop_event is not None and stop_event.is_set():
            raise CancelledError("Routing dispatch stopped after another worker failed")
        names = [name for name in pending.popleft() if name not in accepted]
        if not names:
            continue
        if len(names) == 1:
            name = names[0]
            if single_attempts[name] >= SINGLE_ENTRY_ATTEMPTS:
                continue
            single_attempts[name] += 1
        request = {**payload, row_key: [by_id[name] for name in names]}
        # Charge the actual smaller retry, rather than repeatedly charging the
        # estimate for a full batch. No paid invocation is retried after quota or
        # authentication failures (AgentInvocationError is an AgentOutputError).
        from dataclasses import replace
        from proofmatch.budget import token_cost
        input_tokens = payload_chars(request) // 4 + 1_000
        output_tokens = (60 if row_key == 'chapters' else 80) * len(names)
        budget.require(replace(estimate, input_tokens=input_tokens, output_tokens=output_tokens,
                               usd=token_cost(model, input_tokens, output_tokens)))
        calls += 1
        print(f'  {prompt}: requesting {len(names)} entries, '
              f'{len(request["document"]["blocks"])} blocks, {payload_chars(request)} chars '
              f'(attempt {calls}; {len(accepted)} already preserved)', flush=True)
        try:
            output = _invoke_route(agent, prompt, request, row_key, id_key,
                                   schema['properties'][row_key]['items'], prompt_text)
            valid, errors = _valid_rows(output, request, schema, row_key, id_key)
        except AgentInvocationError:
            raise
        except AgentOutputError as error:
            valid, errors = {}, {name: str(error) for name in names}
        accepted.update(valid)
        last_errors.update(errors)
        if progress is not None:
            _atomic_json(progress, {'version': 1, 'rows': list(accepted.values()),
                                    'remaining_errors': {name: last_errors.get(name, 'Pending')
                                                         for name in expected if name not in accepted}})
        missing = [name for name in names if name not in accepted]
        if missing:
            print(f'  {prompt}: preserved {len(accepted)}/{len(expected)}; '
                  f'retrying {len(missing)} unresolved entries', flush=True)
            width = min(32, max(1, len(missing) // 2))
            pending.extend(missing[start:start + width] for start in range(0, len(missing), width))
    missing = [name for name in expected if name not in accepted]
    if missing:
        raise AgentOutputError(f'{prompt}: {len(missing)} entries remain unresolved after {calls} calls; '
                               f'valid decisions preserved for resume. First: {missing[0]}: '
                               f'{last_errors.get(missing[0], "not processed")}')
    output = {row_key: [accepted[name] for name in expected]}
    validate_against_schema(output, schema)
    if cache is not None:
        _atomic_json(cache, output)
        progress.unlink(missing_ok=True)
    print(f'  {prompt}: {len(expected)} entries, {payload_chars(payload)} chars (saved)', flush=True)
    return output
