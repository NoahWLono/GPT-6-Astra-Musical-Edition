import os,pathlib,resource,subprocess,time,json,signal,hashlib,shutil,sys,math,re
root=pathlib.Path(__file__).resolve().parent
preflight=json.loads((root/'preflight.json').read_text())
sources=root/'sources'; objects=root/'objects'; logs=root/'logs'; logs.mkdir(exist_ok=True)
assert not list(objects.iterdir()),'Fresh objects must be empty'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None
lean=pathlib.Path(preflight['lean_binary']); assert sha(lean)==preflight['lean_binary_sha256']
modules=preflight['modules']+[{'module':'IndependentGoldenFixture','source_sha256':sha(sources/'IndependentGoldenFixture.lean')}]
env=dict(os.environ);env['LEAN_PATH']=':'.join(preflight['lean_path'])
assert str(root.parent) not in preflight['lean_path']
records=[]; aggregate=0; hz=os.sysconf('SC_CLK_TCK'); all_start=time.monotonic()
for item in modules:
    name=item['module'];source=sources/(name+'.lean');out=objects/(name+'.olean');log=logs/(name+'.log')
    assert sha(source)==item['source_sha256']
    assert not out.exists();assert aggregate<180;assert shutil.disk_usage(root).free>=4*1024**3
    cpu_cap=min(20,180-aggregate);watchdog=min(19.5,180-aggregate-.1)
    def limits():
        hard=max(1,int(math.ceil(cpu_cap)))
        resource.setrlimit(resource.RLIMIT_CPU,(hard,hard))
        resource.setrlimit(resource.RLIMIT_FSIZE,(64*1024**2,64*1024**2))
    before=resource.getrusage(resource.RUSAGE_CHILDREN);start=time.monotonic();reason=None;peak=0;observed_cpu=0
    with log.open('wb') as f:
        proc=subprocess.Popen([str(lean),'-j1','-o',str(out),source.name],cwd=sources,env=env,stdout=f,stderr=subprocess.STDOUT,preexec_fn=limits,start_new_session=True)
        while proc.poll() is None:
            wall=time.monotonic()-start
            try:
                pdir=pathlib.Path('/proc')/str(proc.pid)
                stat=(pdir/'stat').read_text();fields=stat[stat.rfind(')')+2:].split()
                observed_cpu=(int(fields[11])+int(fields[12]))/hz
                lines=(pdir/'status').read_text().splitlines()
                rss=int(next(l.split()[1] for l in lines if l.startswith('VmRSS:')))*1024;peak=max(peak,rss)
            except (FileNotFoundError,StopIteration,ProcessLookupError):pass
            output_bytes=sum(x.stat().st_size for x in (out,log) if x.exists())
            if wall>35:reason='wall'
            elif observed_cpu>=watchdog:reason='cpu_watchdog'
            elif peak>2*1024**3:reason='rss'
            elif output_bytes>64*1024**2:reason='output'
            elif shutil.disk_usage(root).free<4*1024**3:reason='disk_floor'
            if reason:
                try:os.killpg(proc.pid,signal.SIGKILL)
                except ProcessLookupError:pass
                break
            time.sleep(.02)
        code=proc.wait()
    after=resource.getrusage(resource.RUSAGE_CHILDREN);cpu=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime;aggregate+=cpu
    content=log.read_text()
    audits={}
    for match in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]",content,re.S): audits[match[1]]=[x.strip() for x in match[2].split(',') if x.strip()]
    for match in re.finditer(r"'([^']+)' does not depend on any axioms",content):audits[match[1]]=[]
    forbidden_axioms={n:xs for n,xs in audits.items() if set(xs)-{'propext','Classical.choice','Quot.sound'}}
    rec={'module':name,'exit_code':code,'stop_reason':reason,'wall_seconds':round(time.monotonic()-start,6),'cpu_seconds':round(cpu,6),'aggregate_cpu_seconds':round(aggregate,6),'observed_cpu_seconds':observed_cpu,'peak_rss_bytes':peak,'source_sha256':sha(source),'object_sha256':sha(out),'log_sha256':sha(log),'axiom_audits':audits,'forbidden_axioms':forbidden_axioms,'command':[str(lean),'-j1','-o',str(out),source.name],'cwd':str(sources),'lean_path':preflight['lean_path'],'limits':{'cpu_watchdog':watchdog,'cpu_hard':cpu_cap,'aggregate_cpu':180,'wall':35,'rss_bytes':2*1024**3,'output_bytes':64*1024**2,'disk_floor_bytes':4*1024**3}}
    records.append(rec);(root/'replay-ledger.json').write_text(json.dumps(records,indent=2)+'\n');(logs/(name+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps({k:rec[k] for k in ['module','exit_code','stop_reason','cpu_seconds','aggregate_cpu_seconds','peak_rss_bytes','forbidden_axioms']}),flush=True)
    if code!=0 or reason or forbidden_axioms or 'declaration uses \'sorry\'' in content or sha(source)!=item['source_sha256']:
        print(content[:12000],flush=True);sys.exit(1)
expected={'AlgebraicTunings.golden_exact_maximum','AlgebraicTunings.goldenMaximumLength_formula','IndependentGoldenAudit.exact_statement'}
assert expected<=set(records[-1]['axiom_audits'])
result={'status':'passed','project_modules':18,'independent_fixture':True,'actual_aggregate_cpu_seconds':round(aggregate,6),'total_wall_seconds':round(time.monotonic()-all_start,6),'peak_sampled_rss_bytes':max(r['peak_rss_bytes'] for r in records),'named_axiom_audit_count':sum(len(r['axiom_audits']) for r in records),'final_axioms':records[-1]['axiom_audits'],'manifest_sha256':preflight['manifest_sha256'],'preflight_sha256':sha(root/'preflight.json'),'fixture_sha256':sha(sources/'IndependentGoldenFixture.lean'),'replay_ledger_sha256':sha(root/'replay-ledger.json'),'trust_boundary':preflight['trust_boundary']}
(root/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
