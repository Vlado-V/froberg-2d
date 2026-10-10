#!/usr/bin/env python3
"""Add the explicitly requested twelve-hour local preflight profile."""
import copy
import json
from pathlib import Path
import sys

root = Path(sys.argv[1])
path = root / 'execution-profiles.json'
data = json.loads(path.read_text())
profile = copy.deepcopy(data['profiles']['palomar-namespace-16x32-v1'])
profile['limits']['job_timeout_minutes'] = 720
profile['limits']['execution_budget_seconds'] = 43200
identifier = 'palomar-namespace-16x32-12h-v1'
data['profiles'][identifier] = profile
path.write_text(json.dumps(data, indent=2) + '\n')
print('Extended preflight: 720-minute job limit; 43200-second verifier budget.')
