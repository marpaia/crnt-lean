#!/usr/bin/env python3
import os,re,subprocess,sys,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[1]
LEAN=os.environ.get('LEAN','/mnt/data/env/lean431-mini/bin/lean')
OUT=ROOT/'.lake/build/lib/lean'; OUT.mkdir(parents=True,exist_ok=True)
ext_paths=[str(p) for p in pathlib.Path('/mnt/data/env/crnt-compiled-cache').glob('*/.lake/build/lib/lean')]
env=os.environ.copy(); env['LEAN_PATH']=':'.join([str(OUT)]+ext_paths)
seen=set(); active=set()
def src(mod):
 p=ROOT/(mod.replace('.','/')+'.lean'); return p if p.exists() else None
def imports(path):
 mods=[]
 for line in path.read_text().splitlines():
  s=line.strip()
  if s.startswith('import '):
   mods += s[len('import '):].split()
 return mods
def build(mod):
 if mod in seen:return True
 if mod in active: raise RuntimeError('cycle '+mod)
 p=src(mod)
 if not p: return True
 out=OUT/(mod.replace('.','/')+'.olean')
 if out.exists() and out.stat().st_mtime >= p.stat().st_mtime:
  seen.add(mod); return True
 active.add(mod)
 for d in imports(p):
  if src(d) and not build(d): return False
 out=OUT/(mod.replace('.','/')+'.olean'); out.parent.mkdir(parents=True,exist_ok=True)
 cmd=[LEAN,'-o',str(out),str(p)]
 print('BUILD',mod,flush=True)
 r=subprocess.run(cmd,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 if r.returncode:
  print(r.stdout,flush=True); return False
 if r.stdout.strip(): print(r.stdout,flush=True)
 active.remove(mod); seen.add(mod); return True
for m in sys.argv[1:]:
 if not build(m): sys.exit(1)
