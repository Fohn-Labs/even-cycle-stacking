import resource,subprocess,sys
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
resource.setrlimit(resource.RLIMIT_CPU,(600,600))
base=Path(__file__).parent
source=base/'verify_cycle.cpp';binary=base/'verify_cycle'
if not binary.exists() or source.stat().st_mtime>binary.stat().st_mtime:
    subprocess.run(['g++','-O3','-std=c++17','-pthread',str(source),'-o',str(binary)],check=True)
result=subprocess.run([str(binary),*sys.argv[1:]],check=True,text=True,capture_output=True)
print(result.stdout,end='')
name='cycle_check_n'+sys.argv[1]+('_sampled' if len(sys.argv)>3 and sys.argv[3]!='0' else '_full')+'.txt'
(base/name).write_text(result.stdout)
