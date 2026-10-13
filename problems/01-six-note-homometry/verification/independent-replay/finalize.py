import json,hashlib,shutil,re
from pathlib import Path
root=Path(__file__).resolve().parent
receipt=json.loads((root/'resource_receipt.json').read_text());author=json.loads((root/'author_frozen_sources.json').read_text());closure=json.loads((root/'full_transitive_import_closure.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert receipt['status']=='all targets passed'
assert receipt['source_hashes_unchanged']
assert len(receipt['runs'])==35
assert all(r['exit_code']==0 and r['stop_reason'] is None for r in receipt['runs'])
original_status={f:sha(root.parent/'lean'/f)==h for f,h in author['source_sha256'].items()}
assert all(original_status.values())
axioms={}
for name in ['FullAudit','ParametricAudit','IndependentExactStatement']:
    s=(root/'logs'/(name+'.log')).read_text()
    for decl,names in re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",s):
        axioms[decl]=[x.strip() for x in names.split(',')]
assert len(axioms)>=5
assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in axioms.values())
summary={'status':'PASS','main_declaration':'OnePitchShift.six_note_one_exchange_existence_iff','independent_fixture':'IndependentHomometryAudit.positive_modulus_exact_statement','main_source_sha256':author['source_sha256']['FullSixNoteExistence.lean'],'author_manifest_sha256':sha(root/'author_frozen_sources.json'),'fixture_source_sha256':sha(root/'sources/IndependentExactStatement.lean'),'fresh_project_modules_compiled':33,'fresh_independent_fixtures_compiled':1,'transitive_source_import_modules':closure['module_count'],'unresolved_source_imports':closure['unresolved_modules'],'original_objects_used':False,'external_libraries_freshly_compiled':False,'mathlib_commit':'905b95818eb32af7874a58b427f50c1711a5e96c','mathlib_tracked_worktree_clean':True,'lean_version':(root/'logs/__version__.log').read_text().strip(),'actual_compiler_cpu_seconds_including_version':receipt['cpu_seconds'],'transitive_source_scan_cpu_seconds':closure['script_cpu_seconds'],'combined_recorded_compiler_and_source_scan_cpu_seconds':receipt['cpu_seconds']+closure['script_cpu_seconds'],'max_compiler_process_cpu_seconds':max(x['cpu_seconds'] for x in receipt['runs']),'max_compiler_process_wall_seconds':max(x['wall_seconds'] for x in receipt['runs']),'max_compiler_process_rss_bytes':max(x['peak_rss_bytes'] for x in receipt['runs']),'total_compiler_log_bytes':sum(x['log_bytes'] for x in receipt['runs']),'remaining_disk_free_bytes':shutil.disk_usage(root).free,'failures':0,'resource_caps_hit':0,'axiom_audits':axioms,'frozen_original_sources_unchanged':original_status,'novelty_established':False,'scope_caveat':'Exact existence of six-element one-exchange homometric dihedrally inequivalent pairs only; no claim of complete six-note homometry classification or formally checked order-four enumeration.'}
(root/'verification.json').write_text(json.dumps(summary,indent=2))
files=['author_frozen_sources.json','source_closure.json','full_transitive_import_closure.json','resource_receipt.json','verification.json','sources/IndependentExactStatement.lean','logs/FullAudit.log','logs/ParametricAudit.log','logs/IndependentExactStatement.log','prepare.py','rebuild_bounded.py','external_closure.py','finalize.py']
(root/'EVIDENCE_SHA256SUMS').write_text(''.join(sha(root/f)+'  '+f+'\n' for f in files))
print(json.dumps({k:summary[k] for k in ['status','actual_compiler_cpu_seconds_including_version','combined_recorded_compiler_and_source_scan_cpu_seconds','max_compiler_process_cpu_seconds','max_compiler_process_wall_seconds','max_compiler_process_rss_bytes','total_compiler_log_bytes','remaining_disk_free_bytes']},indent=2))
