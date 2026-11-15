"""Add type-stabilized readers, reusing the existing public contracts in place."""
from pathlib import Path
import runpy
import difflib

extract = runpy.run_path(str(Path('evidence/tools/frozen_headers.py')))['extract']
path = Path('TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean')
src = path.read_text()
decls = {d['name']: d for d in extract(src)}
params = '''{C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
    (ret : Fin n → State C M) (q₀ : State C M)'''
new = '''/-- A typed view of the existing finite host: its tape count is `K`, its state type
is `State C M`, and its underlying machine is that of `hostTM M K hk ctrl ret q₀`.
The explicit constructor fields keep those types available when `hostTM` is sealed;
this reducible view has exactly the same machine, rather than a new transition table. -/
abbrev hostTMView ''' + params + ''' : FinTM Bool where
  k := K
  State := State C M
  tm := (hostTM M K hk ctrl ret q₀).tm

/-- The typed view is the original bundled host:
`hostTMView M K hk ctrl ret q₀ = hostTM M K hk ctrl ret q₀`. -/
theorem hostTMView_eq ''' + params + ''' :
    hostTMView M K hk ctrl ret q₀ = hostTM M K hk ctrl ret q₀ := rfl

/-- The typed host starts in the supplied state:
`(hostTMView M K hk ctrl ret q₀).tm.q₀ = q₀`. -/
theorem hostTMView_q₀ ''' + params + ''' :
    (hostTMView M K hk ctrl ret q₀).tm.q₀ = q₀ := rfl

'''
wrappers = [
    ('hostTM_step_inl', 'hostTMView_step_inl',
     '''/-- A control step of the typed host applies the supplied action:
for `cfg.state = some (.inl c)`,
`(hostTMView M K hk ctrl ret q₀).tm.step cfg =
(ctrl c cfg.inputSymbol cfg.workTapeSymbols).apply cfg`.
This is `hostTM_step_inl` with explicit tape and state types. -/\n''',
     'hostTM_step_inl M K hk ctrl ret q₀ cfg c hc'),
    ('host_call', 'host_call_view',
     '''/-- A first-halting call of duration `t` transfers to the typed host: all times
`v < t` avoid every control state, and at `t` the seam is at `ret i`, holding
`result` and emitting `pre ++ out`. This is exactly `host_call` for
`hostTMView M K hk ctrl ret q₀`, with its tape and state types explicit. -/\n''',
     'host_call M K hk ctrl ret q₀ i hp x arg result out pre q t hg he'),
    ('host_clean', 'host_clean_view',
     '''/-- A clean call in the typed host reaches `ret i` in some `0 < t ≤ B |arg|`,
holding `f arg`, emitting `pre ++ g arg`, and avoiding every control state
before `t`. This is exactly `host_clean` for `hostTMView M K hk ctrl ret q₀`,
with its tape and state types explicit. -/\n''',
     'host_clean M K hk ctrl ret q₀ i f g B h x arg pre'),
]
for old_name, name, doc, proof in wrappers:
    header = decls[old_name]['header']
    header = header.replace('theorem ' + old_name, 'theorem ' + name, 1)
    header = header.replace('(hostTM M K hk ctrl ret q₀)', '(hostTMView M K hk ctrl ret q₀)')
    new += doc + header.rstrip() + ' :=\n  ' + proof + '\n\n'
assert '\nabbrev hostTMView ' not in src
host_final = src.replace('\nend Turing.ModuleHost', '\n' + new + 'end Turing.ModuleHost')
host_source = src

path = Path('TCSlib/Complexity/Randomized/Build/IterateFindHost.lean')
src = path.read_text()
decls = {d['name']: d for d in extract(src)}
new = '''/-- A typed view of the input copier: one work tape, state type `Fin 2`, and
the existing `copyTM.tm` as its underlying machine. Explicit constructor fields
keep these types available when `copyTM` is sealed. -/
abbrev copyTMView : FinTM Bool where
  k := 1
  State := Fin 2
  tm := copyTM.tm

/-- The typed input copier is the original machine: `copyTMView = copyTM`. -/
theorem copyTMView_eq : copyTMView = copyTM := rfl

/-- The typed copier stays live before `2 * |x| + 2` and reaches the halted seam
holding `x` at that time. This is `copy_clean x` with the one-tape, two-state
types explicit; it adds no copying implementation. -/
'''
header = decls['copy_clean']['header'].replace('lemma copy_clean', 'lemma copy_clean_view', 1)
header = header.replace('copyTM.tm', 'copyTMView.tm')
new += header.rstrip() + ' :=\n  copy_clean x\n\n'
assert '\nabbrev copyTMView ' not in src
copy_final = src.replace('\nend Complexity.IterateFind', '\n' + new + 'end Complexity.IterateFind')
out = Path('/private/tmp/derand-worker/SR-02-proposal')
out.mkdir(parents=True, exist_ok=True)
patch = ''
for rel, before, after in [
    ('TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean', host_source, host_final),
    ('TCSlib/Complexity/Randomized/Build/IterateFindHost.lean', src, copy_final),
]:
    target = out / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(after)
    patch += ''.join(difflib.unified_diff(before.splitlines(keepends=True),
                                        after.splitlines(keepends=True),
                                        fromfile='a/' + rel, tofile='b/' + rel))
(out / 'typed-views.patch').write_text(patch)
print('PREPARATION ONLY: wrote a proposed patch under ' + str(out))
print('No worktree provider file was modified.')
