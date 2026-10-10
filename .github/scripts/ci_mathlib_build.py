#!/usr/bin/env python3
"""Run normal staged Lake builds with bounded aggregate memory and live progress."""
import argparse
import json
import os
from pathlib import Path
import re
import signal
import shutil
import subprocess
import sys
import threading
import time

p=argparse.ArgumentParser()
p.add_argument('--root',type=Path,required=True)
p.add_argument('--guard',type=Path,required=True)
p.add_argument('--logs',type=Path,required=True)
p.add_argument('--job-start',type=float,required=True)
p.add_argument('--preflight',action='store_true')
a=p.parse_args(); root=a.root.resolve(); guard=a.guard.resolve(); logs=a.logs.resolve(); logs.mkdir(parents=True,exist_ok=True)
candidate=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
assert candidate==os.environ['SOURCE_COMMIT'],'candidate source differs from requested commit'
source_metadata={'repository':'Vlado-V/mathlib4','commit':candidate,'toolchain':(root/'lean-toolchain').read_text().strip()}
# Leave time for final reporting before the provider's five-hour job limit.
end=a.job_start+270*60
mem=int(re.search(r'^MemTotal:\s+(\d+)',Path('/proc/meminfo').read_text(),re.M).group(1))*1024
for line in Path('/proc/self/cgroup').read_text().splitlines():
 if line.startswith('0::'):
  directory=Path('/sys/fs/cgroup')/line[3:].lstrip('/')
  while directory==Path('/sys/fs/cgroup') or Path('/sys/fs/cgroup') in directory.parents:
   try:
    raw=(directory/'memory.max').read_text().strip()
    if raw!='max':mem=min(mem,int(raw))
   except OSError:pass
   if directory==Path('/sys/fs/cgroup'):break
   directory=directory.parent
assert mem>=56*1024**3,f'Runner has only {mem} effective bytes'
limits={'memory.high':min(56*1024**3,int(mem*.90)),'memory.max':min(60*1024**3,int(mem*.96)),'memory.swap.max':0,'memory.oom.group':1,'pids.max':8192}
(logs/'capacity.json').write_text(json.dumps({'effective_memory_bytes':mem,'limits':limits,'lake_threads':16,'deadline_epoch':end},indent=2)+'\n')

def guarded_command(bootstrap, command, status, seconds):
 wrapped=[*bootstrap,sys.executable,str(guard/'scripts/supervise_cgroup.py'),'--parent','self','--collect','--deadline',str(seconds),'--grace','30','--cwd',str(root),'--status',str(status)]
 for key,value in limits.items():wrapped+=['--limit',f'{key}={value}']
 child_env={'PATH':os.environ['PATH'],'HOME':os.environ['HOME'],'LEAN_NUM_THREADS':'16','LAKE_NO_CACHE':'true','CI':'true','TERM':'dumb'}
 if 'ELAN_HOME' in os.environ:child_env['ELAN_HOME']=os.environ['ELAN_HOME']
 for key,value in child_env.items():wrapped+=['--setenv',f'{key}={value}']
 return [*wrapped,'--',*command]

def successful_resource(info):
 return (info.get('state')=='finished' and info.get('exit_status')==0
         and info.get('placement_ok') is True and not info.get('launch_error')
         and not info.get('term_signal') and not info.get('deadline_fired')
         and not info.get('liveness_lost') and not info.get('populated_after_kill')
         and all(info.get('limits_applied',{}).get(key) is True for key in limits))

def choose_bootstrap():
 if os.getuid()==0:
  raise SystemExit('Resource guard requires the standard unprivileged runner account; refusing before cache download.')
 delegate=['sudo','-n',sys.executable,str(guard/'scripts/cgroup_delegate.py'),f'--uid={os.getuid()}',f'--gid={os.getgid()}','--']
 candidates=[]
 if Path('/proc/1/comm').read_text().strip()=='systemd':
  candidates.append(('systemd-user',['systemd-run','--user','--scope','--quiet','--property=Delegate=yes','--']))
 candidates.append(('container-delegate',delegate))
 attempts=[]
 for mode,bootstrap in candidates:
  status=logs/(mode+'-probe.json')
  result=subprocess.run(guarded_command(bootstrap,['/usr/bin/true'],status,20),capture_output=True,text=True,timeout=45)
  (logs/(mode+'-probe.log')).write_text(result.stdout+result.stderr)
  try:info=json.loads(status.read_text())
  except (OSError,ValueError):info={}
  attempts.append({'mode':mode,'returncode':result.returncode,'status':info})
  if result.returncode==0 and successful_resource(info):
   (logs/'guard-preflight.json').write_text(json.dumps({'mode':mode,'uid':os.getuid(),'attempts':attempts},indent=2)+'\n')
   print('Resource guard preflight passed: '+mode,flush=True)
   return bootstrap
 (logs/'guard-preflight.json').write_text(json.dumps({'attempts':attempts},indent=2)+'\n')
 raise SystemExit('No working delegated resource scope; see guard probe logs.')

bootstrap=choose_bootstrap()
if a.preflight:raise SystemExit(0)
base=['lake','--rehash','--no-ansi','--fail-fast','build']
q='Archive.Froberg.Quartic.'
stages=[
 ('foundations',base+['Mathlib.RingTheory.MvPolynomial.HomogeneousBasis','Mathlib.RingTheory.MvPolynomial.HomogeneousIdeal','Mathlib.RingTheory.MvPolynomial.LinearFamily','Archive.Froberg.Generic',q+'RankOpen','Archive.Froberg.IndependentStatement']),
 ('large-certificates',base+[q+x+'.Data' for x in ['ProfileCertificate','SharpCertificate','HullCertificate']]),
 ('metadata-products',base+[q+f'FiniteEndpointMetadata{n}Checks' for n in [28,29,30]]+[q+f'FiniteEndpointProductMemo{n}' for n in [28,29,30]]),
 ('inverse-lookups',base+[q+f'FiniteEndpointInverseMemo{n}' for n in [28,29,30]]),
 ('certificate-rows',base+[q+f'FiniteEndpointRows{n}' for n in [28,29,30]]),
 ('full-theorem',base+['Archive.Froberg']),
]
# The final audit uses the compiled theorem and ordinary Lean axiom reporting.
audit=root/'FrobergAxiomAudit.lean'
audit.write_text("""module

public import Lean
public import Archive.Froberg
public import Lean.Util.CollectAxioms

open Lean Elab Command in
elab "#audit_main_dependencies" : command => do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``Froberg.paperStatement, ``Froberg.uniformMainStatement] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {name}"
  logInfo "PASS: main theorem dependencies use only propext, Classical.choice, Quot.sound"

#audit_main_dependencies
#check Froberg.paperStatement
#check Froberg.uniformMainStatement
#print axioms Froberg.paperStatement
#print axioms Froberg.uniformMainStatement
#print FrobergPaper.Statement
#print FrobergPaper.GenericHilbertThrough
#print FrobergPaper.hilbertFunction
#print FrobergPaper.formToRingQuotient
#print FrobergPaper.predictionSeries
#print FrobergPaper.positiveTruncation
""")
shutil.copyfile(audit,logs/'AxiomAudit.lean')
stages.append(('axiom-audit',['lake','env','lean',str(audit)]))
records=[]; active=None; interrupted=False

def stop(signum,frame):
 global interrupted
 interrupted=True
 if active is not None and active.poll() is None:active.terminate()
for sig in [signal.SIGTERM,signal.SIGINT]:signal.signal(sig,stop)

def atomic(path,obj):
 tmp=path.with_suffix(path.suffix+'.tmp');tmp.write_text(json.dumps(obj,indent=2)+'\n');tmp.replace(path)

for stage,command in stages:
 remaining=int(end-time.time())
 if interrupted or remaining<=30:raise SystemExit(124)
 status=logs/(stage+'-resource.json')
 wrapped=guarded_command(bootstrap,command,status,remaining)
 print(f'::group::{stage}',flush=True)
 print('Running '+' '.join(command),flush=True)
 start=time.monotonic(); state={'stage':stage,'command':command,'started_epoch':time.time()}
 with (logs/(stage+'.log')).open('w') as out:
  active=subprocess.Popen(wrapped,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,bufsize=1)
  def consume():
   for line in active.stdout:
    out.write(line);out.flush();print(line,end='',flush=True)
  reader=threading.Thread(target=consume,daemon=True);reader.start()
  while active.poll() is None:
   state['elapsed_seconds']=round(time.monotonic()-start,1)
   try:
    info=json.loads(status.read_text());cg=Path(info.get('cgroup','/no-such-cgroup'))
    state['memory_current']=int((cg/'memory.current').read_text())
    state['memory_peak']=int((cg/'memory.peak').read_text())
   except (OSError,ValueError):pass
   disk=shutil.disk_usage(root)
   state['disk_free_bytes']=disk.free
   state['disk_total_bytes']=disk.total
   cache_disk=shutil.disk_usage(root/'.lake')
   state['cache_free_bytes']=cache_disk.free
   state['cache_total_bytes']=cache_disk.total
   atomic(logs/'progress.json',state)
   with (logs/'progress.jsonl').open('a') as f:f.write(json.dumps(state)+'\n')
   print('Progress '+json.dumps(state),flush=True)
   try:active.wait(timeout=30)
   except subprocess.TimeoutExpired:pass
  reader.join(timeout=10);code=active.returncode
 state.update(returncode=code,elapsed_seconds=round(time.monotonic()-start,1))
 try:state['resource']=json.loads(status.read_text())
 except (OSError,ValueError):state['resource']={}
 records.append(state);atomic(logs/'report.json',{'source':source_metadata,'stages':records,'all_pass':False})
 print('::endgroup::',flush=True)
 if code!=0 or not successful_resource(state['resource']):
  raise SystemExit(code or 1)
 if interrupted:raise SystemExit(143)
text=(logs/'axiom-audit.log').read_text()
if 'PASS: main theorem dependencies use only propext, Classical.choice, Quot.sound' not in text:
 raise SystemExit('Axiom audit did not report its dependency check')
axioms={}
for theorem in ['Froberg.paperStatement','Froberg.uniformMainStatement']:
 m=re.search(re.escape(theorem)+r"['\"]?\s+depends on axioms:\s*\[(.*?)\]",text,re.S)
 if m:used={x.strip() for x in m.group(1).split(',') if x.strip()}
 elif re.search(re.escape(theorem)+r"['\"]?\s+does not depend on any axioms",text):used=set()
 else:raise SystemExit('Missing axiom report for '+theorem)
 if not used<={'propext','Classical.choice','Quot.sound'}:raise SystemExit('Unexpected axioms: '+str(sorted(used)))
 axioms[theorem]=sorted(used)
atomic(logs/'report.json',{'source':source_metadata,'stages':records,'all_pass':True,'axioms':axioms})
print('PASS: complete Archive.Froberg build and main dependency axiom audit.',flush=True)
