#!/usr/bin/env python3
"""Run fresh numerical checks on local Lean declarations.

Each declaration gets a fresh process, hard CPU limits, and an external RSS/time
watchdog. Results stay here; Lean sources are read-only.
By default, select stale annotations; use --name or --all for an explicit rerun.
"""
import argparse
from collections import Counter
from datetime import datetime
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import sys
import time
import traceback
from zoneinfo import ZoneInfo

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
VENDOR = HERE / 'vendor'


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def discover_targets(root, names=None, all_declarations=False):
    rows = []
    requested = set(names or [])
    declaration = re.compile(
        r'^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*'
        r'(?:theorem|lemma|def)\s+([\w\']+)', re.M)
    for path in sorted((root / 'FLMF' / 'Chapter7').rglob('*.lean')):
        text = path.read_text()
        for doc in re.finditer(r'/--(.*?)-/', text, re.S):
            stamp = re.search(r'Numerical:[^\r\n]*', doc[1], re.I)
            if stamp is None:
                continue
            if not requested and not all_declarations and not re.match(
                    r'Numerical:\s*Stale\b', stamp[0], re.I):
                continue
            rest = text[doc.end():]
            match = declaration.search(rest)
            if match is None or any(line.strip() and not line.strip().startswith('--')
                                    for line in rest[:match.start()].splitlines()):
                raise RuntimeError('Cannot associate numerical annotation: ' + str(path))
            if requested and match[1] not in requested:
                continue
            rows.append({
                'name': match[1], 'file': str(path.relative_to(root)),
                'annotation_line': text[:doc.start(1) + stamp.start()].count('\n') + 1,
                'annotation': stamp[0].strip(),
                'source_sha256': sha256(path),
            })
    missing = requested - {row['name'] for row in rows}
    if missing:
        raise ValueError('No numerically annotated declaration found for: ' + ', '.join(sorted(missing)))
    return rows


def worker(args):
    # Set limits before importing the numerical engine. macOS rejects RLIMIT_DATA
    # and RLIMIT_AS limits here, so the parent enforces RSS with its watchdog.
    cap = args.memory_mb * 1024 * 1024
    if sys.platform != 'darwin':
        resource.setrlimit(resource.RLIMIT_DATA, (cap, cap))
        resource.setrlimit(resource.RLIMIT_AS, (cap, cap))
    resource.setrlimit(resource.RLIMIT_CPU, (args.cpu_seconds, args.cpu_seconds + 1))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    targets = json.loads(Path(args.targets).read_text())
    target = targets[args.worker]
    row = dict(target)
    started = time.monotonic()
    try:
        sys.path.insert(0, str(VENDOR))
        import fidelity_extract as checker
        checker.ROOT = Path(args.root) / 'FLMF' / 'Chapter7'
        source = Path(args.root) / target['file']
        if sha256(source) != target['source_sha256']:
            raise RuntimeError('Source changed since target selection')
        matches = [d for d in checker.extract(source) if d['name'] == target['name']]
        if len(matches) != 1:
            row.update(verdict=checker.UNABLE, kind='extraction',
                       detail=f'upstream extractor emitted {len(matches)} matching declarations')
        else:
            declaration = matches[0]
            verdict, kind, detail = checker.classify_and_check(declaration)
            row.update(declaration)
            row.update(verdict=verdict, kind=kind, detail=detail,
                       reused=False, precision_dps=checker.mp.mp.dps,
                       sample_budget_seconds=checker.EVAL_BUDGET)
    except MemoryError:
        row.update(verdict='unable to proceed', kind='memory-limit',
                   detail='worker allocation raised MemoryError')
    except Exception as exc:
        row.update(verdict='unable to proceed', kind='worker-error',
                   detail=f'{type(exc).__name__}: {exc}')
        traceback.print_exc()
    row['elapsed_seconds'] = round(time.monotonic() - started, 3)
    Path(args.result).write_text(json.dumps(row, ensure_ascii=False, indent=2, default=str) + '\n')


def run(args):
    import psutil
    root = Path(args.root).resolve()
    targets = discover_targets(root, args.name, args.all)
    if args.limit:
        targets = targets[:args.limit]
    if not targets:
        print('No Numerical: Stale declarations found. Use --name DECLARATION or --all for a fresh rerun.')
        return
    name = datetime.now(ZoneInfo('America/New_York')).strftime('%Y-%m-%d_%H%M%S_%f')
    output = HERE / 'results' / name
    output.mkdir(parents=True, exist_ok=False)
    targets_path = output / 'targets.json'
    targets_path.write_text(json.dumps(targets, indent=2) + '\n')
    checker_hashes = {str(path.relative_to(HERE)): sha256(path)
                      for path in [Path(__file__).resolve(), *sorted(VENDOR.glob('*.py'))]}
    metadata = {
        'started_at': datetime.now(ZoneInfo('America/New_York')).isoformat(),
        'source_root': str(root), 'selected': len(targets),
        'selection': ('named declarations: ' + ', '.join(args.name) if args.name else
                      'all numerical annotations in FLMF/Chapter7/**/*.lean' if args.all else
                      'all Numerical: Stale annotations in FLMF/Chapter7/**/*.lean'),
        'concurrency': 1, 'memory_mb': args.memory_mb,
        'wall_seconds_per_declaration': args.wall_seconds,
        'cpu_seconds_per_declaration': args.cpu_seconds,
        'watchdog_interval_seconds': 0.1, 'prior_results_reused': False,
        'memory_limit_method': 'external RSS watchdog' if sys.platform == 'darwin'
                               else 'hard heap/address-space limits plus RSS watchdog',
        'python_version': sys.version,
        'dependencies': {n: importlib.metadata.version(n) for n in ('mpmath', 'psutil')},
        'checker_sha256': checker_hashes,
        'source_hashes': {str(p.relative_to(root)): sha256(p)
                          for p in sorted((root / 'FLMF').rglob('*.lean'))},
    }
    (output / 'run.json').write_text(json.dumps(metadata, indent=2) + '\n')
    results = []
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', OPENBLAS_NUM_THREADS='1',
               OMP_NUM_THREADS='1', MKL_NUM_THREADS='1')
    for index, target in enumerate(targets):
        print(f"[{index + 1}/{len(targets)}] checking {target['name']}", flush=True)
        result_path = output / f'{index + 1:02d}_{target["name"]}.json'
        log_path = output / f'{index + 1:02d}_{target["name"]}.log'
        command = [sys.executable, '-I', '-B', str(Path(__file__).resolve()),
                   '--worker', str(index), '--targets', str(targets_path),
                   '--result', str(result_path), '--root', str(root),
                   '--memory-mb', str(args.memory_mb), '--cpu-seconds', str(args.cpu_seconds)]
        started = time.monotonic()
        peak_rss, stop_reason = 0, None
        with log_path.open('w') as log:
            process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT,
                                       env=env, start_new_session=True)
            try:
                tracked = psutil.Process(process.pid)
                while process.poll() is None:
                    try:
                        rss = tracked.memory_info().rss
                        # The numerical engine starts no child processes. Monitor
                        # this known worker directly, without enumerating other
                        # processes on the user's computer.
                        peak_rss = max(peak_rss, rss)
                    except psutil.NoSuchProcess:
                        pass
                    if peak_rss > args.memory_mb * 1024 * 1024:
                        stop_reason = ('memory-limit', f'worker RSS exceeded {args.memory_mb} MB')
                    elif time.monotonic() - started > args.wall_seconds:
                        stop_reason = ('wall-timeout', f'worker exceeded {args.wall_seconds:g} seconds')
                    if stop_reason:
                        os.killpg(process.pid, signal.SIGKILL)
                        break
                    time.sleep(0.1)
                process.wait()
            finally:
                if process.poll() is None:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
        if stop_reason is not None or not result_path.exists():
            if stop_reason is None:
                stop_reason = ('worker-exit', f'worker exited with code {process.returncode} without a result')
            row = {**target, 'verdict': 'unable to proceed', 'kind': stop_reason[0],
                   'detail': stop_reason[1], 'elapsed_seconds': round(time.monotonic() - started, 3)}
        else:
            row = json.loads(result_path.read_text())
        row['peak_rss_mb'] = round(peak_rss / (1024 * 1024), 3)
        row['worker_exit_code'] = process.returncode
        result_path.write_text(json.dumps(row, ensure_ascii=False, indent=2) + '\n')
        results.append(row)
        # Write after every declaration so partial progress survives interruption.
        (output / 'manifest.json').write_text(json.dumps(results, ensure_ascii=False, indent=2) + '\n')
        print(f"  {row['verdict']} [{row['kind']}] {row['detail']} "
              f"({row['elapsed_seconds']}s, peak {row['peak_rss_mb']} MB)", flush=True)
    source_changes = [rel for rel, before in metadata['source_hashes'].items()
                      if sha256(root / rel) != before]
    assert not source_changes, source_changes
    summary = {**dict(Counter(r['verdict'] for r in results)),
               'selected': len(targets), 'completed': len(results),
               'peak_worker_rss_mb': max(r['peak_rss_mb'] for r in results),
               'source_files_unchanged': True,
               'finished_at': datetime.now(ZoneInfo('America/New_York')).isoformat()}
    (output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    lines = ['Fresh numerical check of local Lean declarations',
             json.dumps(summary, ensure_ascii=False), '',
             'Every result below is reported verbatim; unable to proceed means NOT numerically checked.', '']
    for row in results:
        lines.append(f"{row['file']}:{row['annotation_line']} {row['name']}\n"
                     f"  {row['verdict']} | kind={row['kind']} | detail={row['detail']}")
    (output / 'report.txt').write_text('\n'.join(lines) + '\n')
    (HERE / 'results' / 'latest.json').write_text(json.dumps({'run': name, 'summary': summary}, indent=2) + '\n')
    print('Saved results:', output, flush=True)
    print(json.dumps(summary), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', default=str(ROOT))
    parser.add_argument('--memory-mb', type=int, default=512)
    parser.add_argument('--wall-seconds', type=float, default=90)
    parser.add_argument('--cpu-seconds', type=int, default=85)
    parser.add_argument('--limit', type=int)
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument('--name', action='append', help='check a short declaration name; repeat for several')
    selection.add_argument('--all', action='store_true', help='rerun every numerical annotation, regardless of status')
    parser.add_argument('--worker', type=int)
    parser.add_argument('--targets')
    parser.add_argument('--result')
    args = parser.parse_args()
    if args.limit is not None and args.limit <= 0:
        parser.error('--limit must be positive')
    if args.worker is not None:
        worker(args)
    else:
        try:
            run(args)
        except ValueError as exc:
            parser.error(str(exc))


if __name__ == '__main__':
    main()
