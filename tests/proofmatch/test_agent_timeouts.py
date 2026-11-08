import os
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import patch

from proofmatch.agents import Agent, AgentInvocationError, run_isolated


class AgentTimeoutTests(unittest.TestCase):
    def test_timeout_retries_and_preserves_success(self):
        calls = []

        def runner(command, **kwargs):
            calls.append(kwargs['timeout'])
            if len(calls) == 1:
                raise subprocess.TimeoutExpired(command, kwargs['timeout'])
            return subprocess.CompletedProcess(command, 0, 'success', '')

        with patch.dict(os.environ, PROOFMATCH_AGENT_TIMEOUT_SECONDS='12'), \
                patch('proofmatch.agents.time.sleep'):
            result = Agent(runner=runner, backend='codex')._invoke(['fake'], '', '/tmp')
        self.assertEqual(calls, [12, 12])
        self.assertEqual(result.stdout, 'success')

    def test_repeated_timeout_fails_after_three_attempts(self):
        calls = []
        with patch('proofmatch.agents.time.sleep'):
            def runner(command, **kwargs):
                calls.append(command)
                raise subprocess.TimeoutExpired(command, kwargs['timeout'])
            with self.assertRaisesRegex(AgentInvocationError, 'retries exhausted'):
                Agent(runner=runner, backend='codex')._invoke(['fake'], '', '/tmp')
        self.assertEqual(len(calls), 3)

    def test_invalid_timeout_is_rejected(self):
        for value in ['0', '-1', 'nan', 'inf']:
            with self.subTest(value=value), patch.dict(os.environ, PROOFMATCH_AGENT_TIMEOUT_SECONDS=value):
                with self.assertRaises(ValueError):
                    Agent()

    def test_timeout_kills_child_holding_output_pipe(self):
        with tempfile.TemporaryDirectory() as tmp:
            pidfile = Path(tmp) / 'child.pid'
            program = (
                'import subprocess,sys,time,pathlib; '
                'p=subprocess.Popen([sys.executable,"-c","import time; time.sleep(60)"]); '
                f'pathlib.Path({str(pidfile)!r}).write_text(str(p.pid)); '
                'time.sleep(60)'
            )
            started = time.monotonic()
            with self.assertRaises(subprocess.TimeoutExpired):
                run_isolated([sys.executable, '-c', program], input='', capture_output=True,
                             text=True, timeout=1)
            self.assertLess(time.monotonic() - started, 5)
            child = Path('/proc') / pidfile.read_text() / 'stat'
            if child.exists():
                self.assertEqual(child.read_text().split()[2], 'Z')

    def test_normal_completion_and_exit_failure(self):
        result = run_isolated([sys.executable, '-c', 'print(input())'], input='hello',
                              capture_output=True, text=True, check=True, timeout=3)
        self.assertEqual(result.stdout, 'hello\n')
        with self.assertRaises(subprocess.CalledProcessError):
            run_isolated([sys.executable, '-c', 'raise SystemExit(2)'],
                         capture_output=True, text=True, check=True, timeout=3)
