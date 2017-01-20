import re
import sys
import os, os.path
import subprocess
import traceback
import pdb
import SCons.Util
import atexit

# TODO:
#  - switch over to Dafny/Vale tools for dependency generation, rather than regex

Import("*")
  

target_arch='x86'
target_x='86'
sha_arch_dir=''
aes_arch_dir=''
if sys.platform == 'win32' and os.getenv('PLATFORM')=='X64':
  target_arch='amd64'
  target_x='64'
  sha_arch_dir='sha-x64'
  aes_arch_dir='aes-x64'
envDict = {'TARGET_ARCH':target_arch,
           'X':target_x,
           'ARCH':'src/arch/x$X',
           'SHA_ARCH_DIR':sha_arch_dir,
           'AES_ARCH_DIR':aes_arch_dir}

env = Environment(**envDict)
env['DAFNY'] = File('tools/Dafny/Dafny.exe')
env['KREMLIN'] = File('#tools/Kremlin/Kremlin.native')
env['VALE'] = File('bin/vale.exe')
if sys.platform == 'win32':
  env.Replace(CCPDBFLAGS='/Zi /Fd${TARGET.base}.pdb')
  env.Append(CCFLAGS=['/Ox', '/Gz'])
  if os.getenv('PLATFORM')=='X64':
    env['AS'] = 'ml64'
else:
  env.Append(CCFLAGS=['-O3', '-flto', '-g'])
  env['MONO'] = 'mono'

# Convert NUMBER_OF_PROCESSORS into '-j n'.
#num_cpu = int(os.environ.get('NUMBER_OF_PROCESSORS', 1)) 
#SetOption('num_jobs', num_cpu) 

# Retrieve tool-specific command overrides passed in by the user
AddOption('--DARGS',
  dest='dafny_user_args',
  type='string',
  default=[],
  action='append',
  help='Supply temporary additional arguments to the Dafny compiler')
AddOption('--VARGS',
  dest='vale_user_args',
  type='string',
  default=[],
  action='append',
  help='Supply temporary additional arguments to the Vale compiler')
AddOption('--KARGS',
  dest='kremlin_user_args',
  type='string',
  default=[],
  action='append',
  help='Supply temporary additional arguments to the Kremlin compiler')
AddOption('--CARGS',
  dest='c_user_args',
  type='string',
  default=[],
  action='append',
  help='Supply temporary additional arguments to the C compiler')
env['DAFNY_USER_ARGS'] = GetOption('dafny_user_args')
env['VALE_USER_ARGS'] = GetOption('vale_user_args')
env['KREMLIN_USER_ARGS'] = GetOption('kremlin_user_args')
env.Append(CCFLAGS=GetOption('c_user_args'))

# Useful Dafny command lines
dafny_default_args =   '/ironDafny /allocated:1 /compile:0 /timeLimit:30 /trace'
dafny_default_args_nonlarith = dafny_default_args + ' /noNLarith'

####################################################################
#
#   General-purpose utility commands
#
####################################################################

def formatExceptionInfo(maxTBlevel=5):
   cla, exc, trbk = sys.exc_info()
   excName = cla.__name__
   try:
       excArgs = exc.__dict__["args"]
   except KeyError:
       excArgs = "<no args>"
   excTb = traceback.format_tb(trbk, maxTBlevel)
   return (excName, excArgs, excTb)
         
def docmd(env, cmd):
  try:
    print('cmd ' + cmd)
    pipe = SCons.Action._subproc(env, cmd,
                                 stdin = 'devnull',
                                 stderr = 'devnull',
                                 stdout = subprocess.PIPE)  
    print('back from cmd')
  except:
    e = sys.exc_info()[0]
    print ("Error invoking: %s" % cmd)
    print formatExceptionInfo()
    #print ("Exception: %s" % e)
    Exit(1)
  result = []
  line = pipe.stdout.readline()
  while line:
    print('Adding line ' + line)
    result.append(line)
    line = pipe.stdout.readline()
  print('finished docmd')
  return result

def make_cygwin_path(path):
  cygwin_path = docmd("cygpath", path.rstrip()) 
  return cygwin_path[0]

def replace_extension(path, new_ext):
  return "%s.%s" % (os.path.splitext(path)[0], new_ext)

####################################################################
#
#   Define a Vale transformation Builder
#
####################################################################

# add vale.exe and its dependent DLLs to the source list, so a change
# in any one of them causes the target to rebuild.
def vale_tool_dependency_Emitter(target, source, env):
  source.append(vale_deps)
  return (target, source)
  
# add env.Vale(), to invoke Vale to compile a .vad to a .gen.dfy
def add_vale_builder(env):
  vale_builder = Builder(action = "$MONO $VALE -includeSuffix .vad .gen.dfy -in $SOURCE -out $TARGET $VALE_USER_ARGS",
                            suffix = '.gen.dfy',
                            src_suffix = '.vad',
                            emitter=vale_tool_dependency_Emitter)

  env.Append(BUILDERS = {'Vale' : vale_builder})

vale_dfy_include_re = re.compile(r'include verbatim\s+"(\S+)"', re.M)
vale_vad_include_re = re.compile(r'include\s+"(\S+)"', re.M)

def vale_file_scan(node, env, path):
    contents = node.get_text_contents()
    dirname =  os.path.dirname(str(node))

    dfy_includes = vale_dfy_include_re.findall(contents)
    vad_includes = vale_vad_include_re.findall(contents)

    print "Processing %s.  Dir = %s.  vad_includes are %s." % (node, dirname, vad_includes)

    v_dfy_includes = map(lambda f : os.path.join(dirname, os.path.splitext(f)[0] + '.vdfy'), dfy_includes)
    v_vad_includes = map(lambda f : os.path.join(dirname, os.path.splitext(f)[0] + '.vdfy'), vad_includes)
    print "v_dfy_includes: %s" % v_dfy_includes
    print "v_vad_includes: %s" % v_vad_includes

    for i in dfy_includes:
      v = os.path.join(dirname.replace('src', 'obj'), os.path.splitext(i)[0] + '.vdfy')
      f = os.path.join(dirname, i)
      print("Adding Dafny(%s, %s)" % (v, f))
      env.Dafny(v, f)
    for i in vad_includes:
      v = os.path.join(dirname, os.path.splitext(i)[0] + '.vdfy').replace('src', 'obj')
      f = os.path.join(dirname, i)
      print "Adding Vale(%s, %s)" % (v, f)
      env.Vale(v, f)

    files = env.File(v_dfy_includes + v_vad_includes) 
    for f in files:
      print "Returning %s" % f
    return files

#vale_scan = Scanner(function = vale_file_scan,
#                     skeys = ['.vad'])
#env.Append(SCANNERS = vale_scan)


####################################################################
#
#   Dafny-specific utilities
#
####################################################################

### Could try adding this to the scanner below...
### From: http://stackoverflow.com/questions/241327/python-snippet-to-remove-c-and-c-comments
##def comment_remover(text):
##    def replacer(match):
##        s = match.group(0)
##        if s.startswith('/'):
##            return " " # note: a space and not an empty string
##        else:
##            return s
##    pattern = re.compile(
##        r'//.*?$|/\*.*?\*/|\'(?:\\.|[^\\\'])*\'|"(?:\\.|[^\\"])*"',
##        re.DOTALL | re.MULTILINE
##    )
##    return re.sub(pattern, replacer, text)
##
## This picks up on any include statement, even those commented out :(
dafny_include_re = re.compile(r'include\s+"(\S+)"', re.M)

# helper to look up a Dafny BuildOptions matching a srcpath, from the 
# verify_options[] list, dealing with POSIX and Windows pathnames, and 
# falling back on a default if no specific override is present.
def get_build_options(srcpath):
  srcpath = os.path.normpath(srcpath)  # normalize the path, which, on Windows, switches to \\ separators
  srcpath = srcpath.replace('\\', '/') # switch to posix path separators
    
  if srcpath in verify_options:
    return verify_options[srcpath]
  else:
    ext = os.path.splitext(srcpath)[1]
    if ext in verify_options:
      return verify_options[ext]
    else:
      return None

# Scan a .dfy file to discover its dependencies, and add .vdfy targets for each.
# Returns a list of File representing the discovered .dfy dependencies.      
def dafny_file_scan(node, env, path):
    #print("Scanning " + str(node))
    contents = node.get_text_contents()
    dirname =  os.path.dirname(str(node))
    #output = docmd(env, '$DAFNY /nologo /ironDafny /noVerify /printIncludes:Transitive /deprecation:0 /noNLarith ' + str(node))
    #for o in output:
    #  print("Output " + o)
    
    includes = dafny_include_re.findall(contents)
    #includes = []
    v_includes = []
    for i in includes:
      srcpath = os.path.join(dirname, i)
      # TODO : this should convert the .gen.dfy filename back to a src\...\.vad filename, and look up its options
      options = get_build_options(srcpath)
      f = os.path.join(dirname, os.path.splitext(i)[0] + '.vdfy').replace('src', 'obj')
      v_includes.append(f)
      if options != None:
        #print("Adding dependency on " + f)
        options.env.Dafny(f, srcpath)
    return env.File(v_includes)

# Add env.dafny_scan(), to automatically scan .dfy files for dependencies
dafny_scan = Scanner(function = dafny_file_scan,
                     skeys = ['.dfy'])
env.Append(SCANNERS = dafny_scan)

####################################################################
#
#   Define some Dafny transformation Builders
#
####################################################################

# Pseudo-builder that takes Dafny code verifies it
# Arguments:
#  targetfile - the target .vdfy to generate, as a string
#  sourcefile - the .dfy file to verify, as a string or File()
# Return:
#  File representing the verification result
def verify_dafny(env, targetfile, sourcefile):
  temptargetfile = os.path.splitext(targetfile)[0] + '.tmp'
  temptarget = env.Command(temptargetfile, sourcefile, "$MONO $DAFNY $DAFNY_VERIFIER_FLAGS $DAFNY_Z3_PATH $SOURCE $DAFNY_USER_ARGS >$TARGET")
  return env.CopyAs(source=temptarget, target=targetfile)
  
# Add env.Dafny(), to verify a .dfy file into a .vdfy
def add_dafny_verifier(env):
  env.AddMethod(verify_dafny, "Dafny")
  
# Add env.DafnyCompile(), to compile without verification, a .dfy file into a .exe
def add_dafny_compiler(env):
  env['DAFNY_COMPILER_FLAGS'] = '/nologo /noVerify /compile:2'
  dafny_compiler = Builder(action='$MONO $DAFNY $DAFNY_COMPILER_FLAGS $SOURCE /out:$TARGET $DAFNY_USER_ARGS',
                           suffix = '.exe',
                           src_suffix = '.dfy')

  env.Append(BUILDERS = {'DafnyCompile' : dafny_compiler})

# Add env.DafnyKremlin(), to compile without verification, a .dfy file into a Kremlin .json.  
def add_dafny_kremlin(env):
  env['DAFNY_KREMLIN_FLAGS'] = dafny_default_args_nonlarith + ' /nologo /kremlin /noVerify /compile:2 /spillTargetCode:1'
  dafny_kremlin = Builder(action='$MONO $DAFNY $DAFNY_KREMLIN_FLAGS $SOURCE /out:$TARGET $DAFNY_USER_ARGS',
                           suffix = '.json',
                           src_suffix = '.dfy')

  env.Append(BUILDERS = {'DafnyKremlin' : dafny_kremlin})

# Custom emitter for Kremlin .json->.c that also notes the generation of the matching .h file  
def kremlin_emitter(target, source, env):
  c_name = str(target[0])
  h_name = os.path.splitext(c_name)[0]+'.h'
  target.append(h_name)
  return target, source

# Add env.Kremlin(), to extract .c/.h from .json.  The builder returns
# two targets, the .c file first, followed by the .h file.
def add_kremlin(env):
  env['KREMLIN_FLAGS'] = '-warn-error +1..4 -warn-error @4 -skip-compilation -add-include \\"DafnyLib.h\\"'
  kremlin = Builder(action='cd ${TARGET.dir} && ${KREMLIN.abspath} $KREMLIN_FLAGS ${SOURCE.file} $KREMLIN_USER_ARGS',
                           suffix = '.c',
                           src_suffix = '.json',
                           emitter = kremlin_emitter)

  env.Append(BUILDERS = {'Kremlin' : kremlin})

# Pseudo-builder that takes Dafny code and extracts it via Kremlin
# Arguments:
#  kremlin_dfys - a list of .dfy files to extract to C
# Return:
#  A set of targets, two per dfy, the first for the .c file and the second for the .h file
def extract_dafny_code(env, kremlin_dfys):
  kremlin_outputs = []
  for k in kremlin_dfys:
    # generate .json from .dfy
    json_file = os.path.splitext(k.replace('src', 'obj'))[0]+'.json' # dest is in obj\ dir and has .json extension instead of .dfy
    json = env.DafnyKremlin(source=k, target=json_file)
    # generate .c from .json
    json_split = os.path.split(json_file) # [0] is the pathname, [1] is the filename
    target_path = json_split[0]
    json_file = json_split[1]
    target_file_base = os.path.join(target_path, os.path.splitext(json_file)[0].replace('.', '_'))
    target_file_c = target_file_base+'.c'
    target_file_h = target_file_base+'.h'
    outputs = env.Kremlin(source=json, target=target_file_c)
    kremlin_outputs.append(outputs)
  return kremlin_outputs
  
# Compile Vale .vad to Dafny .gen.dfy  
# Takes a source .vad file as a string
# Returns a File() representing the resulting .gen.dfy file
def compile_vale(env, source_vad):
  decls = env.Vale(source='$ARCH/decls.vad', target='obj/arch/x$X/decls.tmp.dfy')
  decls_gen_dfy = env.CopyAs(source='obj/arch/x$X/decls.tmp.dfy', target='obj/arch/x$X/decls.gen.dfy')
  target_s = os.path.splitext(source_vad.replace('src', 'obj').replace('tools', 'obj'))[0]+'.gen.dfy'
  target_dfy = env.Vale(source=source_vad, target=target_s)
  Depends(target_dfy, decls_gen_dfy)
  return target_dfy
  
# Pseudo-builder that takes Vale code, a main .dfy, and generates a Vale EXE which then emits .asm files
# Arguments:
#  vads - a list of vad files to extract
#  vad_main_dfy - the main .dfy used to drive extraction
#  output_base_name - the base name to use for the EXE and ASM files, such as "sha256" to generate "obj\sha256.asm/.s"
# Return:
#  Multiple targets, which are the assembly source files for all platforms.  The first one is the correct file for 
#  the current OS platform (ie. the .s file when running on a POSIX OS, or the .asm on Windows).  The subsequent
#  ones are for other OS platforms, in no particular order.
def extract_vale_code(env, vads, vad_main_dfy, output_base_name):
  # generate decls.gen.dfy from decls.vad
  decls = env.Vale(source='$ARCH/decls.vad', target='obj/arch/x$X/decls.tmp.dfy')
  decls_gen_dfy = env.CopyAs(source='obj/arch/x$X/decls.tmp.dfy', target='obj/arch/x$X/decls.gen.dfy')
  vale_outputs = []
  for s in vads:
    outputs = compile_vale(env, s)
    vale_outputs.append(File(env.subst(s)))
  output_target_base = 'obj/'+output_base_name
  ionative = os.path.normpath('src/lib/util/IoNative.cs')
  exe_name = output_target_base+'.exe'
  exe = env.Clone(DAFNY_COMPILER_FLAGS=dafny_default_args_nonlarith + ' /nologo /noVerify /compile:2 '+ionative).DafnyCompile(
    source=vad_main_dfy, target=exe_name)
  Depends(exe, ionative)
  Depends(exe, decls_gen_dfy)
  Depends(exe, vale_outputs) # todo: this should be implicitly generated by scanning the vad_main_dfy file.  Is it?
  
  masm_win = env.Command(output_target_base+'.asm', exe, '$MONO $SOURCE MASM Win > $TARGET')
  gcc_win = env.Command(output_target_base+'-gcc.S', exe, '$MONO $SOURCE GCC Win > $TARGET')
  gcc_linux = env.Command(output_target_base+'-linux.S', exe, '$MONO $SOURCE GCC Linux > $TARGET')
  gcc_macos = env.Command(output_target_base+'-macos.S', exe, '$MONO $SOURCE GCC MacOS > $TARGET')
  
  if sys.platform.startswith('linux'):
    return [gcc_linux, masm_win, gcc_win, gcc_macos]
  elif sys.platform == 'win32':
    return [masm_win, gcc_win, gcc_linux, gcc_macos]
  elif sys.platform == 'cygwin':
    return [gcc_win, masm_win, gcc_linux, gcc_macos]
  elif sys.platform == 'darwin':
    return [gcc_macos, gcc_win, masm_win, gcc_linux]
  else:
    print('Unsupported sys.platform value: ' + sys.platform)
  
# build and execute a test app
# inputs - set of files to build into the resulting exe
# include_dir - an extra include directory - usually the path to the kremlin-generated headers
# output_base_name - base filename (no path, no extension) to build into the obj\ directory
# returns the exe target and the stdout after executing the exe test target
def build_test(env, inputs, include_dir, output_base_name):
  testenv = env.Clone()
  testenv.Append(CPPPATH=['tools/Kremlin/kremlib', 'src/lib/util', include_dir])
  inputs_obj = []
  for inp in inputs:
    inps = str(inp)
    if inps.startswith('src/'):
      inp = env.CopyAs(source=inp, target=inps.replace('src/', 'obj/', 1))
    inputs_obj.append(inp)
  exe = testenv.Program(source=inputs_obj, target='obj/'+output_base_name+'.exe')
  testoutput = 'obj/'+output_base_name+'.txt'
  env.Command(target=testoutput,
              source=exe,
              action = [exe, 'type NUL > ' + testoutput])
  a = env.Alias('runtest', '', exe)
  #AlwaysBuild(a)
  return a
  
# Add pseudobuilders to env.  
def add_extract_code(env):
  env.AddMethod(extract_vale_code, "ExtractValeCode")
  env.AddMethod(extract_dafny_code, "ExtractDafnyCode")
  env.AddMethod(build_test, "BuildTest")

# Helper class used by the src/SConscript file, to specify per-file
# Dafny command-line options for verification.  
class BuildOptions:
  def __init__(self, args):
    self.env = env.Clone(DAFNY_VERIFIER_FLAGS=args)

# Verify a set of Dafny files by creating verification targets for each,
# which in turn causes a dependency scan to verify all of their dependencies.
def verify_dafny_files(env, files):
  for f in files:
    options = get_build_options(f)
    if options != None:
      target = os.path.splitext(f.replace('src', 'obj'))[0] + '.vdfy'
      target = target.replace('tools', 'obj')  # remap files from tools\Vale\test to obj\Vale\test
      options.env.Dafny(target, f)

# Verify a set of Vale files by creating verification targets for each,
# which in turn causes a dependency scan to verify all of their dependencies.
def verify_vale_files(env, files):
  for f in files:
    options = get_build_options(f)
    if options != None:
      target = os.path.splitext(f.replace('src', 'obj'))[0] + '.vdfy'
      target = target.replace('tools', 'obj')  # remap files from tools\Vale\test to obj\Vale\test
      dfy = compile_vale(env, f)
      options.env.Dafny(target, dfy)

# Verify *.dfy and *.vad files in a list of directories.  This enumerates
# all files in those trees, and creates verification targets for each,
# which in turn causes a dependency scan to verify all of their dependencies.
def verify_files_in(env, directories):
  for d in directories:
    files = Glob(d+'/*.dfy', strings=True)
    verify_dafny_files(env, files)
    files = Glob(d+'/*.vad', strings=True)
    verify_vale_files(env, files)
    
####################################################################
#
#   Put it all together
#
####################################################################
add_dafny_verifier(env)
add_dafny_compiler(env)
add_dafny_kremlin(env)
add_vale_builder(env)
add_kremlin(env)
add_extract_code(env)
env.AddMethod(verify_files_in, "VerifyFilesIn")
env.AddMethod(verify_vale_files, "VerifyValeFiles")
env.AddMethod(verify_dafny_files, "VerifyDafnyFiles")

#
# Pull in the SConscript files which define actual build targets:
#

# Export identifiers to make them visible inside SConscript files
Export('env', 'BuildOptions', 'dafny_default_args', 'dafny_default_args_nonlarith')

# Include the SConscript files themselves
vale_tool_results = SConscript('tools/Vale/SConscript')
vale_deps = vale_tool_results.dependencies;
env['Z3'] = vale_tool_results.z3
if sys.platform == 'win32':
  env['DAFNY_Z3_PATH'] = '' # use the default Boogie search rule, which uses Z3 from the tools/Dafny directory
else:  
  env['DAFNY_Z3_PATH'] = '/z3exe:$Z3'

SConscript('./SConscript')

# Import identifiers defined inside SConscript files, which the SConstruct consumes
Import(['verify_options', 'verify_paths'])

env.VerifyFilesIn(verify_paths)

# extract a string filename out of a build failure
def bf_to_filename(bf):
    import SCons.Errors
    if bf is None: # unknown targets product None in list
        return '(unknown tgt)'
    elif isinstance(bf, SCons.Errors.StopError):
        return str(bf)
    elif bf.node:
        return str(bf.node)
    elif bf.filename:
        return bf.filename
    return '(unknown failure)'

def report_verification_failures():
    from SCons.Script import GetBuildFailures
    bf = GetBuildFailures()
    if bf:
        # bf is normally a list of build failures; if an element is None,
        # it's because of a target that scons doesn't know anything about.
        for x in bf:
          if x is not None:
            filename = bf_to_filename(x)
            if filename.endswith('.tmp'):
              print '##### Verification error.  Printing contents of ' + filename + ' #####'
              with open (filename, 'r') as myfile:
                lines = myfile.read().splitlines()
                for line in lines:
                  print line

def display_build_status():
    report_verification_failures()

atexit.register(display_build_status)
