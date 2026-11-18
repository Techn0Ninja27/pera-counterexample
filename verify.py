"""Build the pinned Lean project and record an explicit axiom audit."""
import argparse
import datetime
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

HERE=Path(__file__).resolve().parent
ALLOWED_AXIOMS={'propext','Classical.choice','Quot.sound'}

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def verify(output):
    if output.exists(): raise FileExistsError('Preserve previous verification; choose a fresh output directory')
    output.mkdir(parents=True)
    files=[HERE/'PeraVerification.lean',HERE/'Audit.lean',*sorted((HERE/'PeraVerification').glob('*.lean'))]
    for p in files:
        text=p.read_text()
        if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',text):
            raise ValueError(f'Prohibited proof escape or declaration in {p.name}')
    lake=shutil.which('lake') or str(Path.home()/'.elan/bin/lake')
    commands=[('build',[lake,'build']),('axioms',[lake,'env','lean','Audit.lean']),('version',[lake,'env','lean','--version'])]
    logs={};codes={}
    for name,cmd in commands:
        run=subprocess.run(cmd,cwd=HERE,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        logs[name]=run.stdout;codes[name]=run.returncode
        (output/(name+'.log')).write_text(run.stdout)
        if run.returncode: break
    expected=json.loads((HERE/'theorems.json').read_text())
    found={}
    for name,body in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",logs.get('axioms','')):
        found[name]=[x.strip() for x in body.split(',') if x.strip()]
    checked=(len(codes)==3 and all(c==0 for c in codes.values()) and set(found)==set(expected)
             and all(set(xs)<=ALLOWED_AXIOMS for xs in found.values()))
    record={'schema':'pera-lean-verification.v1','date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'status':'verified' if checked else 'verification_failed','command_exit_codes':codes,
            'theorem_axioms':found,'expected_theorems':expected,
            'allowed_standard_axioms':sorted(ALLOWED_AXIOMS),
            'source_sha256':{str(p.relative_to(HERE)):sha(p) for p in files},
            'toolchain':(HERE/'lean-toolchain').read_text().strip(),
            'manifest_sha256':sha(HERE/'lake-manifest.json'),'lakefile_sha256':sha(HERE/'lakefile.toml'),
            'verifier_sha256':sha(Path(__file__)),
            'log_sha256':{n:sha(output/(n+'.log')) for n in logs},
            'scope':'Lean checked the listed formal statements using the pinned mathlib dependency. Paper-to-statement translation and downstream usefulness are separate claims.',
            'task_usefulness_established':False,'novelty_established':False}
    (output/'result.json').write_text(json.dumps(record,indent=2)+'\n')
    if not checked: raise RuntimeError('Verification failed; logs and result retained')
    print(json.dumps({'status':record['status'],'theorems':len(found),'output':str(output)}))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True)
    verify(ap.parse_args().output.resolve())
