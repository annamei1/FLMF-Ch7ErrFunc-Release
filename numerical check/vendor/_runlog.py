#!/usr/bin/env python3
"""Append-only run log for the agent's DAG / validation scripts — one timestamped line per
invocation recording what it did. Local-only (gitignored): it's run history for debugging
("when was the manifest last regenerated? did the DAG change?"), not shared state.

    tail agent/runs/activity.log
"""
import datetime
import pathlib

LOG = pathlib.Path(__file__).resolve().parent / "runs" / "activity.log"


def log(script, summary):
    """Append `<ISO-time>  <script>  <summary>` to agent/runs/activity.log. Best-effort —
    logging must never break the tool, so all errors are swallowed."""
    try:
        LOG.parent.mkdir(parents=True, exist_ok=True)
        ts = datetime.datetime.now().isoformat(timespec="seconds")
        with open(LOG, "a") as f:
            f.write(f"{ts}  {script:22s} {summary}\n")
    except Exception:
        pass
