#!/usr/bin/env python3
"""Seed matching Mathlib artifacts from an unchanged official checkout."""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

p=argparse.ArgumentParser()
p.add_argument('--root',type=Path,required=True)
p.add_argument('--upstream',type=Path,required=True)
p.add_argument('--logs',type=Path,required=True)
a=p.parse_args(); root=a.root.resolve(); upstream=a.upstream.resolve(); a.logs.mkdir(parents=True,exist_ok=True)
expected='aa4180fd65f90dd50307a354941dfbee635cf9d2'
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=upstream,text=True).strip()
assert head==expected,(head,expected)
candidate=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
assert candidate==os.environ['SOURCE_COMMIT'],'candidate source differs from requested commit'
for name in ['lean-toolchain','lake-manifest.json']:
 assert (root/name).read_bytes()==(upstream/name).read_bytes(),name
# Existing Mathlib source must be unchanged. The three additional files have no
# upstream cache entry and will be built normally in the candidate checkout.
for source in (upstream/'Mathlib').rglob('*.lean'):
 rel=source.relative_to(upstream)
 assert source.read_bytes()==(root/rel).read_bytes(),str(rel)
u=(upstream/'lakefile.lean').read_text(); r=(root/'lakefile.lean').read_text()
for start,end in [('package mathlib where','/-!\n## Mathlib libraries'),('abbrev mathlibOnlyLinters','/-- These options are passed as `leanOptions` when building `MathlibTest`'),('@[default_target]\nlean_lib Mathlib','-- NB. When adding further libraries')]:
 def piece(t):
  i=t.index(start);return t[i:t.index(end,i)]
 assert piece(u)==piece(r),'Mathlib compiler configuration changed'
imports=set()
visited=set()
def collect(path):
 if path in visited:return
 visited.add(path)
 for name in re.findall(r'^(?:public )?(?:meta )?import (?:all )?([A-Za-z0-9_.]+)',path.read_text(),re.M):
  if name=='Mathlib' or name.startswith('Mathlib.'):
   relative=Path(*name.split('.')).with_suffix('.lean')
   if (upstream/relative).is_file():imports.add(name)
   elif (root/relative).is_file():collect(root/relative)
   else:raise RuntimeError('Missing Mathlib import '+name)
for path in (root/'Archive/Froberg').rglob('*.lean'):collect(path)
assert imports,'No official cache roots were found'
print(f'Fetching the unchanged official Mathlib cache for {len(imports)} direct import roots.',flush=True)
with (a.logs/'official-cache.log').open('w') as out:
 proc=subprocess.Popen(['lake','exe','cache','get','--cache-from=master',*sorted(imports)],cwd=upstream,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 for line in proc.stdout:
  out.write(line);out.flush();print(line,end='',flush=True)
 code=proc.wait()
 if code:raise SystemExit(code)
# Keep full traces, IR, and oleans. Never copy the compiled lakefile/config.
for source,target in [(upstream/'.lake/packages',root/'.lake/packages'),(upstream/'.lake/build',root/'.lake/build')]:
 target.mkdir(parents=True,exist_ok=True)
 subprocess.run(['cp','-a','--reflink=auto',str(source)+'/.',str(target)+'/'],check=True)
(a.logs/'seed.json').write_text(json.dumps({'official_upstream':head,'candidate_commit':candidate,'cache_roots':sorted(imports),'method':'standard official cache plus intact artifact copy; normal Lake rehash follows','existing_mathlib_sources_identical':True,'mathlib_options_identical':True},indent=2)+'\n')
