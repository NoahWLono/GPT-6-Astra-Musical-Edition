import os,sys,time,json,hashlib,resource,subprocess,shutil,signal
from pathlib import Path
import psutil
root=Path(__file__).resolve().parent
replay=json.loads((root/'resource_receipt.json').read_text())
assert replay['status']=='all targets passed','Wait for the fresh compiler replay'
assert not (root/'fixture_resource_receipt.json').exists(),'Never overwrite fixture evidence'
remaining=400-replay['cpu_seconds'];limit=min(19.5,remaining-.05)
assert limit>0 and shutil.disk_usage(root).free>=4*1024**3
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=root/'independent_fixture_audit.py';log=root/'fixture.log';start=time.monotonic();peak=0;why=None
prior_output=sum(x.stat().st_size for x in (root/'logs').glob('*.log'))
def pre():
 os.setsid();resource.setrlimit(resource.RLIMIT_CPU,(20,20));resource.setrlimit(resource.RLIMIT_FSIZE,(64*1024**2,64*1024**2))
with log.open('w') as f:
 p=subprocess.Popen([sys.executable,str(source)],cwd=root,stdout=f,stderr=subprocess.STDOUT,preexec_fn=pre)
 while True:
  got,status,ru=os.wait4(p.pid,os.WNOHANG)
  if got:break
  try:
   proc=psutil.Process(p.pid);procs=[proc]+proc.children(recursive=True)
   cpu=sum(x.cpu_times().user+x.cpu_times().system for x in procs)
   rss=sum(x.memory_info().rss for x in procs);peak=max(peak,rss)
   if cpu>=limit:why='CPU watchdog'
   elif rss>=2*1024**3:why='RSS watchdog'
   elif time.monotonic()-start>=35:why='wall watchdog'
   elif prior_output+log.stat().st_size>=64*1024**2:why='output watchdog'
   elif shutil.disk_usage(root).free<4*1024**3:why='disk watchdog'
   if why:os.killpg(p.pid,signal.SIGKILL);got,status,ru=os.wait4(p.pid,0);break
  except psutil.NoSuchProcess:pass
  time.sleep(.01)
 code=os.waitstatus_to_exitcode(status);p.returncode=code
cpu=ru.ru_utime+ru.ru_stime;wall=time.monotonic()-start;peak=max(peak,ru.ru_maxrss*1024)
if why is None:
 if cpu>=limit:why='CPU cap exceeded at completion'
 elif peak>=2*1024**3:why='RSS cap exceeded at completion'
 elif wall>=35:why='wall cap exceeded at completion'
 elif prior_output+log.stat().st_size>=64*1024**2:why='output cap exceeded at completion'
r={'status':'passed' if code==0 and why is None else 'stopped','command':[sys.executable,str(source)],'exit_code':code,'stop_reason':why,'cpu_seconds':cpu,'wall_seconds':wall,'peak_rss_bytes':peak,'aggregate_cpu_seconds_including_replay':replay['cpu_seconds']+cpu,'source_sha256':sha(source),'log_sha256':sha(log),'inherited_limits':{k:v for k,v in replay.items() if k.endswith('_limit_seconds') or k.endswith('_limit_bytes') or k.endswith('_floor_bytes') or k.startswith('per_process')}}
(root/'fixture_resource_receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2));print(log.read_text());sys.exit(0 if code==0 and why is None else 1)
