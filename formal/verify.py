"""Compile every local proof and audit its kernel dependencies. Run from formal/."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
OUT = ROOT.parent / 'verification'
OUT.mkdir(exist_ok=True)
modules = sorted((ROOT / 'Atlas').glob('*.lean'))
names = []
for p in modules:
    text = p.read_text(encoding='utf-8-sig')
    clean = re.sub(r'/-.*?-/', '', text, flags=re.S)
    clean = re.sub(r'--[^\n]*', '', clean)
    if re.search(r'\b(sorry|admit|axiom|unsafe)\b', clean):
        raise SystemExit(f'Unfinished or unchecked declaration in {p.name}')
    namespace = re.search(r'^namespace\s+(\S+)', clean, re.M).group(1)
    names.extend(namespace + '.' + n for n in re.findall(r'\b(?:theorem|lemma)\s+(\w+)', clean))

(ROOT / 'Atlas.lean').write_text(''.join(f'import Atlas.{p.stem}\n' for p in modules), encoding='utf-8')
(ROOT / 'AxiomAudit.lean').write_text('import Atlas\n' + ''.join(f'#print axioms {n}\n' for n in names), encoding='utf-8')
log = []
checks = []
def run(args):
    result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, encoding='utf-8', errors='replace')
    output = result.stdout + result.stderr
    log.append('$ ' + ' '.join(args) + '\n' + output)
    checks.append({'command': args, 'exit_code': result.returncode})
    print('PASS' if result.returncode == 0 else 'FAIL', ' '.join(args), flush=True)
    if result.returncode or re.search(r'\bsorryAx\b', output):
        (OUT / 'lean-verification.log').write_text('\n'.join(log), encoding='utf-8')
        raise SystemExit(output)
    return output

version = run(['lake', 'env', 'lean', '--version']).strip()
build = ROOT / '.lake' / 'build' / 'lib' / 'lean'
(build / 'Atlas').mkdir(parents=True, exist_ok=True)
for p in modules:
    run(['lake', 'env', 'lean', '-o', str(Path('.lake/build/lib/lean/Atlas') / (p.stem + '.olean')), str(p.relative_to(ROOT))])
run(['lake', 'env', 'lean', '-o', '.lake/build/lib/lean/Atlas.olean', 'Atlas.lean'])
audit = run(['lake', 'env', 'lean', 'AxiomAudit.lean'])
dependencies = set()
for group in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', audit, re.S):
    dependencies.update(s.strip() for s in group.split(',') if s.strip())
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
if not dependencies <= allowed:
    raise SystemExit(f'Unexpected proof dependencies: {dependencies - allowed}')
inputs = modules + [ROOT / 'Atlas.lean', ROOT / 'AxiomAudit.lean', ROOT / 'lakefile.lean', ROOT / 'lake-manifest.json', ROOT / 'lean-toolchain']
report = {
    'verified_at': datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=8))).isoformat(),
    'lean_version': version, 'theorem_count': len(names), 'theorems': names,
    'kernel_axioms': sorted(dependencies), 'checks': checks,
    'source_sha256': {str(p.relative_to(ROOT)).replace('\\', '/'): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},
    'scope': 'Only the exact Lean statements listed here are verified. See docs/proofs/README.md for manuscript coverage and remaining gaps.'
}
(OUT / 'lean-verification.log').write_text('\n'.join(log), encoding='utf-8')
(OUT / 'verification.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print(f'Verified {len(names)} declarations; allowed kernel axioms only.', flush=True)
