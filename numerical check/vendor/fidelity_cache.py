#!/usr/bin/env python3
"""Incremental-sweep cache: skip re-checking statements already verified.

Both fidelity sweeps (`fidelity_extract.py` Tier-1, `fidelity_tier2.py` Tier-2)
can be expensive — Tier-1 is CPU-heavy mpmath, Tier-2 spends real money on LLM
calls. When a statement was already verified on a previous run AND has not changed
since, re-checking it is pure waste.

This module lets a sweep reuse a prior verdict, keyed on a CONTENT HASH of the
statement. The hash is the safety mechanism: if the statement text changes at all,
the hash changes, the cache misses, and the sweep re-checks it. This preserves the
project's live-derived "promotes AND demotes" guarantee — a statement that was
edited and no longer passes is never silently carried forward as verified.

The prior manifest itself is the cache (no separate cache file): each manifest row
already records the statement content and the verdict it earned.

A hash of the *statement* alone does NOT see changes to the checking engine — new
`oracle_bindings.py` anchors, a fixed checker, or a different judge model. A
statement can stay byte-identical while the verdict it *should* get changes. So
skipping is paired with an ENGINE FINGERPRINT: a hash of the files that decide
verdicts (the checker + its anchors for Tier-1; the prompts + model names for
Tier-2). When the fingerprint changes, the cache auto-invalidates for one full
re-validation, then resumes skipping. This makes "skip verified by default" safe:
an engine change can never silently carry a stale verdict forward.

A manual full re-check is still available via `--recheck-all` (alias
`--recheck-verified`).
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

# Verdicts that mean "statement-fidelity verified" — only these are skippable.
VERIFIED_VERDICTS = {"PASS", "FAITHFUL"}


def stmt_hash(*parts) -> str:
    """Stable content hash over the pieces that define a statement's check.

    Non-string parts are canonicalized with sorted-key JSON so dict ordering
    never perturbs the hash.
    """
    h = hashlib.sha1()
    for p in parts:
        if isinstance(p, str):
            blob = p
        else:
            blob = json.dumps(p, sort_keys=True, ensure_ascii=False, default=str)
        h.update(blob.encode("utf-8"))
        h.update(b"\x00")
    return h.hexdigest()


def tier1_hash(row: dict) -> str:
    """Content hash for a Tier-1 row (works on both a freshly extracted decl and
    a prior manifest row — both carry concl/binders/constraints)."""
    return stmt_hash(
        row.get("concl", ""),
        row.get("binders") or {},
        row.get("constraints") or {},
    )


def tier2_hash(lean_payload: str) -> str:
    """Content hash for a Tier-2 row — the verbatim Lean surface the judge sees."""
    return stmt_hash(lean_payload or "")


def load_prior(path: Path) -> dict:
    """Load a prior manifest as {name: row}; empty dict if absent/unreadable.

    The prior manifest IS the cache: each row carries the statement content
    (so its hash can be recomputed via tier1_hash/tier2_hash) and the verdict it
    earned. No separate cache file is needed."""
    try:
        data = json.loads(Path(path).read_text())
    except (FileNotFoundError, ValueError):
        return {}
    return {r["name"]: r for r in data if isinstance(r, dict) and "name" in r}


# ── engine fingerprint ───────────────────────────────────────────────────────
# The fingerprint is a hash of the inputs that determine what verdict a statement
# earns. If it changes, reuse is disabled for one run (full re-validation) so an
# engine change never carries a stale verdict forward.

def file_hash(path) -> str:
    try:
        return hashlib.sha1(Path(path).read_bytes()).hexdigest()
    except (FileNotFoundError, IsADirectoryError):
        return "absent"


def engine_fingerprint(files=(), extra=()) -> str:
    """Fingerprint over verdict-deciding file contents plus extra strings
    (e.g. model names)."""
    return stmt_hash(*[file_hash(f) for f in files], *[str(x) for x in extra])


def load_fingerprint(store: Path, tier: str):
    """Return the stored fingerprint for `tier`, or None if unknown."""
    try:
        return json.loads(Path(store).read_text()).get(tier)
    except (FileNotFoundError, ValueError):
        return None


def save_fingerprint(store: Path, tier: str, fp: str) -> None:
    store = Path(store)
    try:
        d = json.loads(store.read_text())
        if not isinstance(d, dict):
            d = {}
    except (FileNotFoundError, ValueError):
        d = {}
    d[tier] = fp
    store.parent.mkdir(parents=True, exist_ok=True)
    store.write_text(json.dumps(d, indent=1))
