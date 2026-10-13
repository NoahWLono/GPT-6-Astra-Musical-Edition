import os,sys,time,json,hashlib,resource,subprocess,shutil,signal
from pathlib import Path
import psutil
root=Path(__file__).resolve().parent;src=root/'sources';out=root/'objects';logs=root/'logs'
exe=Path('/workspace/scratch/caabcb85bd83/toolchains/lean-4.32.2-linux/bin/lean')
m=Path('/workspace/scratch/caabcb85bd83/dependencies/mathlib4-v4.32.2')
assert not out.exists(),'fresh objects required; never overwrite replay evidence'
out.mkdir();logs.mkdir()
paths=[out,m/'.lake/build/lib/lean']+sorted((m/'.lake/packages').glob('*/.lake/build/lib/lean'))
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,paths));env.pop('LEAN_SRC_PATH',None)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
order=(root/'REBUILD_ORDER.txt').read_text().splitlines()
state={'status':'running','compiler_slot':2,'aggregate_cpu_limit_seconds':400,'per_process_cpu_watchdog_seconds':19.5,'per_process_hard_cpu_seconds':20,'per_process_wall_seconds':35,'rss_limit_bytes':2*1024**3,'output_limit_bytes':64*1024**2,'disk_floor_bytes':4*1024**3,'lean_path':env['LEAN_PATH'],'lean_executable':str(exe),'lean_executable_sha256':sha(exe),'cpu_seconds':0.0,'runs':[],'sources_sha256':{p.name:sha(p) for p in src.glob('*.lean')},'original_project_objects_reused':0}
state_path=root/'resource_receipt.json'
def save():state_path.write_text(json.dumps(state,indent=2)+'\n')
def pre():
 os.setsid();resource.setrlimit(resource.RLIMIT_CPU,(20,20));resource.setrlimit(resource.RLIMIT_FSIZE,(64*1024**2,64*1024**2))
for name in ['__version__']+order:
 if state['cpu_seconds']>=399.9 or shutil.disk_usage(root).free<4*1024**3:
  state['status']='stopped before next process';save();sys.exit(1)
 limit=min(19.5,399.95-state['cpu_seconds'])
 cmd=[str(exe),'--version'] if name=='__version__' else [str(exe),'-j1','-o',str(out/(name+'.olean')),str(src/(name+'.lean'))]
 log=logs/(name+'.log');t0=time.monotonic();peak=0;why=None
 other_output=sum(p.stat().st_size for p in logs.glob('*.log'));save()
 with log.open('w') as f:
  p=subprocess.Popen(cmd,cwd=src,env=env,stdout=f,stderr=subprocess.STDOUT,preexec_fn=pre)
  while True:
   got,status,ru=os.wait4(p.pid,os.WNOHANG)
   if got:break
   try:
    pp=psutil.Process(p.pid);procs=[pp]+pp.children(recursive=True)
    cpu_sample=sum(x.cpu_times().user+x.cpu_times().system for x in procs)
    rss=sum(x.memory_info().rss for x in procs);peak=max(peak,rss)
    if cpu_sample>=limit:why='CPU watchdog'
    elif rss>=2*1024**3:why='RSS watchdog'
    elif time.monotonic()-t0>=35:why='wall watchdog'
    elif other_output+log.stat().st_size>=64*1024**2:why='output watchdog'
    elif shutil.disk_usage(root).free<4*1024**3:why='disk watchdog'
    if why:
     os.killpg(p.pid,signal.SIGKILL);got,status,ru=os.wait4(p.pid,0);break
   except psutil.NoSuchProcess:pass
   time.sleep(.01)
  code=os.waitstatus_to_exitcode(status);p.returncode=code
 cpu=ru.ru_utime+ru.ru_stime;wall=time.monotonic()-t0;peak=max(peak,ru.ru_maxrss*1024)
 if why is None:
  if cpu>=limit:why='CPU cap exceeded at completion'
  elif peak>=2*1024**3:why='RSS cap exceeded at completion'
  elif wall>=35:why='wall cap exceeded at completion'
  elif other_output+log.stat().st_size>=64*1024**2:why='output cap exceeded at completion'
 rec={'target':name,'command':cmd,'exit_code':code,'cpu_user_seconds':ru.ru_utime,'cpu_system_seconds':ru.ru_stime,'cpu_seconds':cpu,'wall_seconds':wall,'peak_rss_bytes':peak,'stop_reason':why,'log_bytes':log.stat().st_size,'log_sha256':sha(log)}
 if name!='__version__':rec['source_sha256']=sha(src/(name+'.lean'))
 if (out/(name+'.olean')).exists():rec['object_sha256']=sha(out/(name+'.olean'))
 state['cpu_seconds']+=cpu;state['runs'].append(rec);save()
 print(json.dumps({k:rec[k] for k in ['target','exit_code','cpu_seconds','wall_seconds','peak_rss_bytes','stop_reason']}),flush=True)
 if code!=0 or why is not None:
  state['status']='stopped on first failure or resource cap';save();print(log.read_text()[:6000],flush=True);sys.exit(1)
state['status']='all targets passed';state['source_hashes_unchanged']=all(sha(src/k)==v for k,v in state['sources_sha256'].items());save()
print('TOTAL_ACTUAL_CPU_SECONDS',state['cpu_seconds'],flush=True)
