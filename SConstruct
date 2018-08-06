# This file requires Python version >= 3.6
# This file requires SCons version >= 3.00

##################################################################################################
#
# Here are some background notes on SCons for anyone interested in reading or editing this file.
# See https://scons.org/documentation.html for more information.
#
# SCons is a build tool, like Make. Similar to Make, it builds a graph of dependencies and
# commands that should be run when files change.  However, unlike Make, SCons does not have a
# specialized language to describe the graph.  Instead, SCons runs a user-supplied Python script
# named "SConstruct" to construct the graph.  After the script completes, the SCons engine
# uses the constructed graph to analyze dependencies and run commands.  (Note that unlike Make,
# SCons's default dependency analysis uses file hashes rather than timestamps.)
#
# For example, consider the following Makefile:
#
#   b.txt : a1.txt sub/a2.txt
#       cmd1 a1.txt sub\\a2.txt > b.txt
#   c.txt : b.txt
#       cmd2 b.txt > c.txt
#
# The most direct SCons equivalent of this is the following Python code:
#
#   Command('b.txt', ['a1.txt', 'sub/a2.txt'], 'cmd1 a1.txt sub\\a2.txt > b.txt')
#   Command('c.txt', 'b.txt', 'cmd2 b.txt > c.txt')
#
# However, SCons encourages a more platform-neutral style, based on two concepts: nodes and
# environments.  For example, the code above contains a string that is hard-wired to use
# Windows-style backslashes rather than Unix-style forward slashes.  Instead of writing strings,
# SCons allows scripts to construct abstract "nodes" that can represent graph nodes such as files.
# SCons can then convert those nodes into paths with forward or backward slashes depending on
# the platform:
#
#   # First construct File nodes for each file name (using forward slashes, even on Windows):
#   a1 = File('a1.txt')
#   a2 = File('sub/a2.txt')
#   b = File('b.txt')
#   c = File('c.txt')
#   # Then let SCons convert the File nodes into strings:
#   Command(b, [a1, a2], f'cmd1 {a1} {a2} > {b}')
#   Command(c, b, f'cmd2 {b} > {c}')
#
# Scripts can say str(a1), a1.path, a1.abspath, etc. to convert a node to a string.  The code
# above uses Python's f-strings (formatted string literals) to convert nodes to strings and embed
# them into larger strings ( https://docs.python.org/3/whatsnew/3.6.html#pep-498-formatted-string-literals ).
#
# SCons encourages scripts to write functions that accept and pass nodes rather than strings
# For example, the built-in SCons object-file generator will generate an object file node, whose
# actual string representation may be "foo.o" using Unix tools or "foo.obj" using Windows tools:
#
#   foo_c = File('foo.c')
#   foo_obj = Object(foo_c)  # compile foo.c to foo.o or foo.obj
#
# (Note that "foo_obj = Object('foo.c')" is also ok, because most built-in SCons functions
# convert string names to nodes automatically.)
#
# In addition to encouraging platform independence, SCons tries to encourage independence from
# users' configurations.  In particular, by default, it executes commands in a minimal
# environment with a minimal PATH, such as ['/usr/local/bin', '/bin', '/usr/bin'] on Unix.
# The Environment function creates a new minimal environment:
#
#   env = Environment()
#
# Scripts can then customize various environments to change the PATH, change the default
# C/C++/Assembly tools, change the flags passed to various tools, etc:
#
#   env.Append(CCFLAGS=['-O3', '-flto', '-g', '-DKRML_NOUINT128', '-std=c++11'])
#   env.PrependENVPath('PATH', os.path.dirname(str(gmp_dll)))
#
# Built in top-level functions like "Command(...)" and "Object(...)" execute in a default
# environment.  To run them in a custom environment, simply call them as methods of an
# environment object:
#
#   env.Command(b, [a1, a2], f'cmd1 {a1} {a2} > {b}')
#   env.Command(c, b, f'cmd2 {b} > {c}')
#   foo_obj = env.Object(foo_c)
#
# SCons has many other features, but for simplicity, the code in this file uses SCons features
# sparingly, preferring Python features (such as f-strings) to SCons features (such as
# SCons's own string substitution for special variables like $SOURCES) when possible.
# Our hope is that this Python-centric style will be more approachable to newcomers.
#
##################################################################################################

import re
import sys
import os, os.path
import subprocess
import traceback
import pdb
import SCons.Util
import atexit
import platform
import fnmatch
import distutils.dir_util
import shutil

if sys.version_info < (3, 6):
  print(f'Requires Python version >= 3.6, found version {sys.version_info}')  # If the syntax of this line is invalid, the version of Python is probably older than 3.6
  exit(1)

##################################################################################################
#
#   Command-line options
#
##################################################################################################

if 'VALE_HOME' in os.environ:
  vale_default_path = os.environ['VALE_HOME']
else:
  vale_default_path = 'tools/Vale'

if 'KREMLIN_HOME' in os.environ:
  kremlin_default_path = os.environ['KREMLIN_HOME']
else:
  kremlin_default_path = 'tools/Kremlin'

if 'FSTAR_HOME' in os.environ:
  fstar_default_path = os.environ['FSTAR_HOME']
else:
  fstar_default_path = 'tools/FStar'

# Retrieve tool-specific command overrides passed in by the user
AddOption('--VALE-PATH', dest = 'vale_path', type = 'string', default = vale_default_path, action = 'store',
  help = 'Specify the path to Vale tool')
AddOption('--KREMLIN-PATH', dest = 'kremlin_path', type = 'string', default = kremlin_default_path, action = 'store',
  help = 'Specify the path to kreMLin')
AddOption('--FSTAR-PATH', dest = 'fstar_path', type = 'string', default = fstar_default_path, action = 'store',
  help = 'Specify the path to F* tool')
AddOption('--FSTAR-Z3', dest = 'fstar_z3', type = 'string', default = '', action = 'store',
  help = 'Specify the path to z3 or z3.exe for F*')
AddOption('--FSTAR-MY-VERSION', dest = 'fstar_my_version', default = False, action = 'store_true',
  help = 'Use version of F* that does not necessarily match .fstar_version')
AddOption('--FSTAR-Z3-MY-VERSION', dest = 'fstar_z3_my_version', default = False, action = 'store_true',
  help = 'Use version of Z3 that does not necessarily match .fstar_z3_version')
AddOption('--RECORD-HINTS', dest = 'record_hints', default = False, action = 'store_true',
  help = 'Record new F* .hints files into the hints directory')
AddOption('--USE-HINTS', dest = 'use_hints', default = False, action = 'store_true',
  help = 'Use F* .hints files from the hints directory')
AddOption('--FARGS', dest = 'fstar_user_args', type = 'string', default = [], action = 'append',
  help = 'Supply temporary additional arguments to the F* compiler')
AddOption('--VARGS', dest = 'vale_user_args', type = 'string', default = [], action = 'append',
  help = 'Supply temporary additional arguments to the Vale compiler')
AddOption('--KARGS', dest = 'kremlin_user_args', type = 'string', default = [], action = 'append',
  help = 'Supply temporary additional arguments to the Kremlin compiler')
AddOption('--CARGS', dest = 'c_user_args', type = 'string', default = [], action = 'append',
  help = 'Supply temporary additional arguments to the C compiler')
AddOption('--OPENSSL', dest = 'openssl_path', type = 'string', default = None, action = 'store',
  help = 'Specify the path to the root of an OpenSSL source tree')
AddOption('--CACHE-DIR', dest = 'cache_dir', type = 'string', default = None, action = 'store',
  help = 'Specify the SCons Shared Cache Directory')
AddOption('--NO-VERIFY', dest = 'noverify', default = False, action = 'store_true',
  help = 'Verify and compile, or compile only')
AddOption('--ONE', dest = 'single_vaf', type = 'string', default = None, action = 'store',
  help = 'Only verify one specified .vaf file, and in that file, only verify procedures or verbatim blocks marked as {:verify}.')
AddOption('--NO-COLOR', dest='no_color', default=False, action='store_true',
  help="Don't add color to build output")
AddOption('--DUMP-ARGS', dest = 'dump_args', default = False, action = 'store_true',
  help = "Print arguments that will be passed to the verification tools")
AddOption('--FSTAR-EXTRACT', dest = 'fstar_extract', default = False, action = 'store_true',
  help = "Extract .ml files from F* files")
AddOption('--MIN-TEST', dest = 'min_test', default = False, action = 'store_true',
  help = "Only run on a minimal set of test files")

vale_path = Dir(GetOption('vale_path')).abspath
kremlin_path = Dir(GetOption('kremlin_path')).abspath
fstar_path = Dir(GetOption('fstar_path')).abspath
fstar_user_args = GetOption('fstar_user_args')
vale_user_args = GetOption('vale_user_args')
kremlin_user_args = GetOption('kremlin_user_args')
c_user_args = GetOption('c_user_args')
openssl_path = GetOption('openssl_path')
fstar_my_version = GetOption('fstar_my_version')
fstar_z3_my_version = GetOption('fstar_z3_my_version')
fstar_extract = GetOption('fstar_extract')
record_hints = GetOption('record_hints')
use_hints = GetOption('use_hints')
no_color = GetOption('no_color')
dump_args = GetOption('dump_args')
single_vaf = GetOption('single_vaf')
is_single_vaf = not (single_vaf is None)
min_test = GetOption('min_test')

##################################################################################################
#
#   Environment settings
#
##################################################################################################

common_env = Environment()

common_env.Append(CCFLAGS = c_user_args)

target_arch = 'x86'
if (sys.platform == 'win32' and os.getenv('PLATFORM') == 'X64') or platform.machine() == 'x86_64':
  target_arch = 'amd64'

common_env['TARGET_ARCH'] = target_arch

mono = ''
if sys.platform == 'win32':
  import importlib.util
  common_env.Replace(CCPDBFLAGS = '/Zi /Fd${TARGET.base}.pdb')
  # Use kremlib.h without primitive support for uint128_t.
  common_env.Append(CCFLAGS = ['/Ox', '/Gz', '/DKRML_NOUINT128'])
  common_env.Append(LINKFLAGS = ['/DEBUG'])
  if os.getenv('PLATFORM') == 'X64':
    common_env['AS'] = 'ml64'
  if 'SHELL' in os.environ and importlib.util.find_spec('win32job') != None and importlib.util.find_spec('win32api'):
    # Special job handling for cygwin so that child processes exit when the parent process exits
    import win32job
    import win32api
    hdl = win32job.CreateJobObject(None, "")
    win32job.AssignProcessToJobObject(hdl, win32api.GetCurrentProcess())
    extended_info = win32job.QueryInformationJobObject(None, win32job.JobObjectExtendedLimitInformation)
    extended_info['BasicLimitInformation']['LimitFlags'] = win32job.JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE
    win32job.SetInformationJobObject(hdl, win32job.JobObjectExtendedLimitInformation, extended_info)
else:
  common_env.Append(CCFLAGS = ['-O3', '-flto', '-g', '-DKRML_NOUINT128', '-std=c++11'])
  mono = 'mono'

if sys.platform == 'win32':
  # fstar.exe relies on libgmp-10.dll
  gmp_dll = FindFile('libgmp-10.dll', os.environ['PATH'].split(';'))
  if gmp_dll != None:
    common_env.PrependENVPath('PATH', os.path.dirname(str(gmp_dll)))

# Helper class to specify per-file command-line options for verification.
class BuildOptions:
  # First argument is mandatory (verification options); all others are optional named arguments
  def __init__(self, args, vale_includes = None):
    self.env = common_env.Clone()
    self.verifier_flags = args
    self.vale_includes = vale_includes

##################################################################################################
#
#   Configuration settings
#
##################################################################################################

fstar_default_args_nosmtencoding = ('--max_fuel 1 --max_ifuel 1'
  + (' --initial_ifuel 1' if is_single_vaf else ' --initial_ifuel 0')
  # The main purpose of --z3cliopt smt.QI.EAGER_THRESHOLD=100 is to make sure that matching loops get caught
  # Don't remove unless you're sure you've used the axiom profiler to make sure you have no matching loops
  + ' --z3cliopt smt.arith.nl=false --z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3'
  + ' --hint_info'
  + (' --use_hints --use_hint_hashes' if use_hints else '')
  + (' --record_hints' if record_hints else ' --cache_checked_modules')
  + ' --cache_dir obj/cache_checked'
  + ' --use_extracted_interfaces true'
  )
fstar_default_args = (fstar_default_args_nosmtencoding
  + ' --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped'
  )

vale_scons_args = '-disableVerify -omitUnverified' if is_single_vaf else ''
vale_includes = f'-include {File("code/lib/util/operator.vaf")}'

verify_paths = [
  'code',
  'specs',
]

external_files = [
  'obj/external/CanonCommSwaps.fst',
  'obj/external/CanonCommMonoid.fst',
  'obj/external/CanonCommSemiring.fst',
  'obj/external/C.Loops.fst',
  'obj/external/Spec.Loops.fst',
]

no_extraction_files = [File(x) for x in [
  'obj/ml_out/CanonCommMonoid.ml',
  'obj/ml_out/CanonCommSemiring.ml',
  'obj/ml_out/X64_Poly1305_Math.ml',
  'obj/ml_out/Vale_Tactics.ml',
]]

#
# Table of files we exclude from the minimal test suite
# (typically for performance reasons)
# Note that the entries below are prefixes of blacklisted files
#
min_test_suite_blacklist = [File(x) for x in [
  'obj/crypto/aes/x64/X64.GCMencrypt.fst',
  'obj/crypto/aes/x64/X64.GCMdecrypt.fst',
  'obj/thirdPartyPorts/OpenSSL/poly1305/x64/X64.Poly1305.fst',
  'obj/crypto/aes/x64/X64.GHash',
  'obj/crypto/aes/x64/X64.GCTR.fst',
  'obj/crypto/aes/x64/X64.AES.fst'
]]

manual_dependencies = {
  'obj/code/arch/x64/X64.Vale.InsLemmas.fst.verified.tmp': 'obj/code/arch/x64/X64.Vale.Decls.fst',
  'obj/code/arch/x64/X64.Vale.InsBasic.fst.verified.tmp': 'obj/code/arch/x64/X64.Vale.Decls.fst',
  'obj/code/arch/x64/X64.Vale.InsMem.fst.verified.tmp': 'obj/code/arch/x64/X64.Vale.Decls.fst',
  'obj/code/arch/x64/X64.Vale.InsVector.fst.verified.tmp': 'obj/code/arch/x64/X64.Vale.Decls.fst',
  'obj/code/arch/x64/X64.Vale.InsAes.fst.verified.tmp': 'obj/code/arch/x64/X64.Vale.Decls.fst',
  'obj/code/arch/x64/X64.Vale.InsMem.fst.tmp': 'src/code/arch/x64/X64.Memory.fst',
  'obj/code/arch/x64/X64.Vale.InsVector.fst.tmp': 'src/code/arch/x64/X64.Memory.fst',
  'obj/code/arch/x64/X64.Vale.StateLemmas.fsti.tmp': 'src/code/arch/x64/X64.Memory.fst',
  'obj/code/arch/x64/X64.Vale.StateLemmas.fst.tmp': 'src/code/arch/x64/X64.Memory.fst',
  'obj/code/arch/x64/X64.Memory_s.fst.tmp': 'src/code/arch/SecretByte.fst',
}

#
# Table of special-case sources which requires non-default arguments
#
verify_options = [
  ('code/lib/util/operator.vaf', BuildOptions(fstar_default_args, vale_includes = '')),

  # Any use of expose_interfaces requires adding to manual_dependencies
  ('code/arch/x64/X64.Vale.InsLemmas.fst', BuildOptions(fstar_default_args + ' --expose_interfaces X64.Vale.Decls.fst' + ' --expose_interfaces X64.Memory.fst')),
  ('obj/code/arch/x64/X64.Vale.InsBasic.fst', BuildOptions(fstar_default_args + ' --expose_interfaces X64.Vale.Decls.fst' + ' --expose_interfaces X64.Memory.fst')),
  ('obj/code/arch/x64/X64.Vale.InsMem.fst', BuildOptions(fstar_default_args + ' --expose_interfaces X64.Vale.Decls.fst' + ' --expose_interfaces X64.Memory.fst')),
  ('obj/code/arch/x64/X64.Vale.InsVector.fst', BuildOptions(fstar_default_args + ' --expose_interfaces X64.Vale.Decls.fst' + ' --expose_interfaces X64.Memory.fst')),
  ('obj/code/arch/x64/X64.Vale.InsAes.fst', BuildOptions(fstar_default_args + ' --expose_interfaces X64.Vale.Decls.fst' + ' --expose_interfaces X64.Memory.fst')),
  ('code/arch/x64/X64.Vale.StateLemmas.fsti', BuildOptions(fstar_default_args + ' --expose_interfaces X64.Memory.fst')),
  ('code/arch/x64/X64.Vale.StateLemmas.fst', BuildOptions(fstar_default_args + ' --expose_interfaces X64.Memory.fst')),
  ('code/arch/x64/X64.Vale.Lemmas.fsti', BuildOptions(fstar_default_args + ' --expose_interfaces X64.Memory.fst')),
  ('code/arch/x64/X64.Vale.Lemmas.fst', BuildOptions(fstar_default_args + ' --expose_interfaces X64.Memory.fst')),
  ('code/arch/x64/X64.Vale.Decls.fst', BuildOptions(fstar_default_args + ' --expose_interfaces X64.Memory.fst')),

  # Special treatment for sensitive modules
  ('code/arch/x64/X64.Leakage_Ins.fst', BuildOptions(fstar_default_args_nosmtencoding)),

  # Disable verification by adding 'filename': None
  ('code/crypto/aes/x64/Low.GCMencrypt.fst', None), # TODO: timeout in gcm_core
  ('code/thirdPartyPorts/Intel/aes/x64/X64.AESCTR.vaf', None), # TODO: slow

  # Interop stubs
  ('code/arch/x64/interop/AESEncryptBlock_win.fst', BuildOptions(fstar_default_args_nosmtencoding.replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100', '').replace('--use_extracted_interfaces true', '').replace('--z3cliopt smt.arith.nl=false', '') + '--smtencoding.elim_box true ' + ' --expose_interfaces SecretByte.fst --expose_interfaces X64.Memory_s.fst --expose_interfaces X64.Memory.fst')),
  ('code/arch/x64/interop/AESEncryptBE_win.fst', BuildOptions(fstar_default_args_nosmtencoding.replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100', '').replace('--use_extracted_interfaces true', '').replace('--z3cliopt smt.arith.nl=false', '') + '--smtencoding.elim_box true ' + ' --expose_interfaces SecretByte.fst --expose_interfaces X64.Memory_s.fst --expose_interfaces X64.Memory.fst')),
  ('code/arch/x64/interop/Gcm_load_xor_win.fst', BuildOptions(fstar_default_args_nosmtencoding.replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100', '').replace('--use_extracted_interfaces true', '').replace('--z3cliopt smt.arith.nl=false', '') + '--smtencoding.elim_box true ' + ' --expose_interfaces SecretByte.fst --expose_interfaces X64.Memory_s.fst --expose_interfaces X64.Memory.fst')),
  ('code/arch/x64/interop/Gcm_make_length_win.fst', BuildOptions(fstar_default_args_nosmtencoding.replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100', '').replace('--use_extracted_interfaces true', '').replace('--z3cliopt smt.arith.nl=false', '') + '--smtencoding.elim_box true ' + ' --expose_interfaces SecretByte.fst --expose_interfaces X64.Memory_s.fst --expose_interfaces X64.Memory.fst')),
  ('code/arch/x64/interop/GCTR_win.fst', BuildOptions(fstar_default_args_nosmtencoding.replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100', '').replace('--use_extracted_interfaces true', '').replace('--z3cliopt smt.arith.nl=false', '') + '--smtencoding.elim_box true ' + ' --expose_interfaces SecretByte.fst --expose_interfaces X64.Memory_s.fst --expose_interfaces X64.Memory.fst')),
  ('code/arch/x64/interop/GHash_extra_win.fst', BuildOptions(fstar_default_args_nosmtencoding.replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100', '').replace('--use_extracted_interfaces true', '').replace('--z3cliopt smt.arith.nl=false', '') + '--smtencoding.elim_box true ' + ' --expose_interfaces SecretByte.fst --expose_interfaces X64.Memory_s.fst --expose_interfaces X64.Memory.fst')),
  ('code/arch/x64/interop/GHash_one_block_win.fst', BuildOptions(fstar_default_args_nosmtencoding.replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100', '').replace('--use_extracted_interfaces true', '').replace('--z3cliopt smt.arith.nl=false', '') + '--smtencoding.elim_box true ' + ' --expose_interfaces SecretByte.fst --expose_interfaces X64.Memory_s.fst --expose_interfaces X64.Memory.fst')),
  ('code/arch/x64/interop/GHash_stdcall_win.fst', BuildOptions(fstar_default_args_nosmtencoding.replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100', '').replace('--use_extracted_interfaces true', '').replace('--z3cliopt smt.arith.nl=false', '') + '--smtencoding.elim_box true ' + ' --expose_interfaces SecretByte.fst --expose_interfaces X64.Memory_s.fst --expose_interfaces X64.Memory.fst')),
  ('code/arch/x64/interop/Inc32_win.fst', BuildOptions(fstar_default_args_nosmtencoding.replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100', '').replace('--use_extracted_interfaces true', '').replace('--z3cliopt smt.arith.nl=false', '') + '--smtencoding.elim_box true ' + ' --expose_interfaces SecretByte.fst --expose_interfaces X64.Memory_s.fst --expose_interfaces X64.Memory.fst')),
  ('code/arch/x64/interop/Mk_quad32_1_win.fst', BuildOptions(fstar_default_args_nosmtencoding.replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100', '').replace('--use_extracted_interfaces true', '').replace('--z3cliopt smt.arith.nl=false', '') + '--smtencoding.elim_box true ' + ' --expose_interfaces SecretByte.fst --expose_interfaces X64.Memory_s.fst --expose_interfaces X64.Memory.fst')),
  ('code/arch/x64/interop/Quad32_xor_win.fst', BuildOptions(fstar_default_args_nosmtencoding.replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100', '').replace('--use_extracted_interfaces true', '').replace('--z3cliopt smt.arith.nl=false', '') + '--smtencoding.elim_box true ' + ' --expose_interfaces SecretByte.fst --expose_interfaces X64.Memory_s.fst --expose_interfaces X64.Memory.fst')),
  ('code/arch/x64/interop/Reverse_quad32_win.fst', BuildOptions(fstar_default_args_nosmtencoding.replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100', '').replace('--use_extracted_interfaces true', '').replace('--z3cliopt smt.arith.nl=false', '') + '--smtencoding.elim_box true ' + ' --expose_interfaces SecretByte.fst --expose_interfaces X64.Memory_s.fst --expose_interfaces X64.Memory.fst')),
  ('code/arch/x64/interop/Zero_quad32_win.fst', BuildOptions(fstar_default_args_nosmtencoding.replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100', '').replace('--use_extracted_interfaces true', '').replace('--z3cliopt smt.arith.nl=false', '') + '--smtencoding.elim_box true ' + ' --expose_interfaces SecretByte.fst --expose_interfaces X64.Memory_s.fst --expose_interfaces X64.Memory.fst')),

  #'src/thirdPartyPorts/OpenSSL/poly1305/x64/X64.Poly1305.vaf': None,

  ('code/*/*.fst', BuildOptions(fstar_default_args)),
  ('code/*/*.fsti', BuildOptions(fstar_default_args)),
  ('specs/*/*.fst', BuildOptions(fstar_default_args)),
  ('specs/*/*.fsti', BuildOptions(fstar_default_args)),

  # .fst/.fsti files default to this set of options
  ('.fst', BuildOptions(fstar_default_args + ' --use_two_phase_tc false')),
  ('.fsti', BuildOptions(fstar_default_args + ' --use_two_phase_tc false')),

  # Needed to significantly speed up verification of interop files (and use the checked Memory_s.fst with expose_interfaces)
  ('code/arch/x64/Views.fst', BuildOptions(fstar_default_args.replace('--smtencoding.nl_arith_repr wrapped', '--smtencoding.nl_arith_repr native') + ' --expose_interfaces SecretByte.fst')),
  ('code/arch/x64/X64.Bytes_Semantics.fst', BuildOptions(fstar_default_args.replace('--smtencoding.nl_arith_repr wrapped', '--smtencoding.nl_arith_repr native') + ' --expose_interfaces SecretByte.fst')),

  ('code/lib/collections/Collections.Lists.fst', BuildOptions(fstar_default_args.replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100',''))),
  ('code/crypto/poly1305/x64/X64.Poly1305.Util.fst', BuildOptions(fstar_default_args_nosmtencoding)),
  ('code/crypto/poly1305/x64/X64.Poly1305.Util.fsti', BuildOptions(fstar_default_args_nosmtencoding)),
  ('code/arch/x64/X64.Memory_s.fst', BuildOptions(fstar_default_args_nosmtencoding.replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100', '').replace('--use_extracted_interfaces true', '').replace('--z3cliopt smt.arith.nl=false', '') + '--smtencoding.elim_box true ' + ' --expose_interfaces SecretByte.fst')),
  ('code/arch/x64/Interop.fst', BuildOptions(fstar_default_args_nosmtencoding.replace('--use_extracted_interfaces true', '').replace('--z3cliopt smt.QI.EAGER_THRESHOLD=100', '') + '--smtencoding.elim_box true ')),
  ('code/arch/Memory_s.fst', BuildOptions(fstar_default_args.replace('--use_extracted_interfaces true', ''))),
  ('code/lib/util/BufferViewHelpers.fst' , BuildOptions(fstar_default_args_nosmtencoding.replace('--z3cliopt smt.arith.nl=false', ''))),

  # We copy these files from F*'s library because we need to generate a .checked file for them,
  # but we don't need to reverify them:
  ('obj/external/*.fst', BuildOptions('--cache_checked_modules --admit_smt_queries true')),

  # .vaf files default to this set of options when compiling .fst/.fsti
  ('.vaf', BuildOptions(fstar_default_args + ' --use_two_phase_tc false'))
]

verify_options_dict = { k:v for (k,v) in verify_options}

# --NOVERIFY is intended for CI scenarios, where the Win32/x86 build is verified, so
# the other build flavors do not redundently re-verify the same results.
fstar_no_verify = ''
verify = (GetOption('noverify') == False)
if not verify:
  print('***\n*** WARNING:  NOT VERIFYING ANY CODE\n***')
  fstar_no_verify = '--lax'

# Find Z3 for F*
found_z3 = False
if verify:
  fstar_z3 = GetOption('fstar_z3')
  if fstar_z3 == '':
    fstar_z3 = File('tools/Z3/z3.exe').path if sys.platform == 'win32' else 'tools/Z3/z3'
    if os.path.isfile(fstar_z3):
      found_z3 = True
    else:
      if sys.platform == 'win32':
        find_z3 = FindFile('z3.exe', os.environ['PATH'].split(';'))
      else:
        find_z3 = FindFile('z3', os.environ['PATH'].split(':'))
      if find_z3 != None:
        found_z3 = True
        fstar_z3 = str(find_z3)
  else:
    found_z3 = True
  fstar_z3_path = '--smt ' + fstar_z3
else:
  fstar_z3_path = ''

vale_exe = File(f'{vale_path}/bin/vale.exe')
fstar_exe = File(f'{fstar_path}/bin/fstar.exe')

##################################################################################################
#
#   Global variables
#
##################################################################################################

all_modules = []  # string names of modules
src_include_paths = []  # string paths in sources where .fst, .fsti are found
obj_include_paths = []  # string paths in obj/, but omitting the 'obj/' prefix
ml_out_deps = {}
fsti_map = {}  # map module names to .fsti File nodes (or .fst File nodes if no .fsti exists)

# match 'include {:attr1} ... {:attrn} "filename"'
# where attr may be 'verbatim' or 'from BASE'
vale_include_re = re.compile(r'include((?:\s*\{\:(?:\w|[ ])*\})*)\s*"(\S+)"', re.M)
vale_from_base_re = re.compile(r'\{\:\s*from\s*BASE\s*\}')
vale_open_re = re.compile(r'open\s+([a-zA-Z0-9_.]+)')
vale_import_re = re.compile(r'module\s+[a-zA-Z0-9_]+\s*[=]\s*([a-zA-Z0-9_.]+)')

if (not sys.stdout.isatty()) or no_color:
  # No color if the output is not a terminal or user opts out
  yellow = ''
  red = ''
  uncolor = ''
else:
  yellow = '\033[93m'
  red = '\033[91;40;38;5;217m'
  uncolor = '\033[0m'

##################################################################################################
#
#   Utility functions
#
##################################################################################################

def print_error(s):
  print(f'{red}{s}{uncolor}')

def print_error_exit(s):
  print_error(s)
  Exit(1)

# Given a File node for dir/dir/.../m.extension, return m
def file_module_name(file):
  return os.path.splitext(file.name)[0]

# Return '.vaf', '.fst', etc.
def file_extension(file):
  return os.path.splitext(file.path)[1]

# Drop the '.vaf', '.fst', etc.
def file_drop_extension(file):
  return os.path.splitext(file.path)[0]

# Given source File node, return File node in object directory
def to_obj_dir(file):
  if str(file).startswith('obj'):
    return file
  else:
    return File(f'obj/{file}')

def to_hint_file(file):
  return File(f'hints/{file.name}.hints')

def ml_out_file(sourcefile, suffix):
  module_name = file_module_name(sourcefile).replace('.', '_')
  return File(f'obj/ml_out/{module_name}{suffix}')

# Is the file from our own sources, rather than an external file (e.g., like an F* library file)?
def is_our_file(file):
  path = file.path
  return True in [path.startswith(str(Dir(p))) for p in ['obj'] + verify_paths]

def compute_include_paths(src_include_paths, obj_include_paths, obj_prefix):
  return src_include_paths + [str(Dir('obj/external'))] + [str(Dir(f'{obj_prefix}/{x}')) for x in obj_include_paths]

def compute_includes(src_include_paths, obj_include_paths, obj_prefix):
  fstar_include_paths = compute_include_paths(src_include_paths, obj_include_paths, obj_prefix)
  return " ".join(["--include " + x for x in fstar_include_paths])

def CopyFile(target, source):
  Command(target, source, Copy(target, source))
  return target

##################################################################################################
#
#   Configuration and environment functions
#
##################################################################################################

# Helper to look up a BuildOptions matching a srcpath File node, from the
# verify_options[] list, falling back on a default if no specific override is present.
def get_build_options(srcnode):
  srcpath = srcnode.path
  srcpath = srcpath.replace('\\', '/')  # switch to posix path separators
  if srcpath in verify_options_dict:    # Exact match
    return verify_options_dict[srcpath]
  else:
    for key, options in verify_options: # Fuzzy match
      if fnmatch.fnmatch (srcpath, key):
        return options
    ext = os.path.splitext(srcpath)[1]
    if ext in verify_options_dict:      # Exact extension match
      return verify_options_dict[ext]
    else:
      return None

def on_black_list(file, list):
  return True in [str(file).startswith(str(entry)) for entry in list]

def check_fstar_version():
  import subprocess
  fstar_version_file = ".fstar_version"
  if os.path.isfile(fstar_version_file):
    with open(fstar_version_file, 'r') as myfile:
      lines = myfile.read().splitlines()
    version = lines[0]
    cmd = [str(fstar_exe), '--version']
    o = subprocess.check_output(cmd, stderr = subprocess.STDOUT).decode('ascii')
    lines = o.splitlines()
    for line in lines:
      if '=' in line:
        key, v = line.split('=', 1)
        if key == 'commit' and v == version:
          return
    print_error(f'Expected F* version commit={version}, but fstar --version returned the following:')
    for line in lines:
      print_error('  ' + line)
    print_error_exit(f'Get F* version {version} from https://github.com/FStarLang/FStar, modify .fstar_version, or use the --FSTAR-MY-VERSION option to override')

def check_z3_version(fstar_z3):
  import subprocess
  z3_version_file = ".fstar_z3_version"
  if os.path.isfile(z3_version_file):
    with open(z3_version_file, 'r') as myfile:
      lines = myfile.read().splitlines()
    version = lines[0]
    versions = version.split('.')
    cmd = [fstar_z3, '--version']
    o = subprocess.check_output(cmd, stderr = subprocess.STDOUT).decode('ascii')
    lines = o.splitlines()
    line = lines[0]
    for word in line.split(' '):
      if '.' in word:
        nums = word.split('.')
        higher = False
        lower = False
        for i in range(min(len(nums), len(versions))):
          if nums[i] < versions[i]:
            lower = True
            break
          if nums[i] > versions[i]:
            higher = True
            break
        if higher or (not lower and len(nums) >= len(versions)):
          return
        break
    print_error(f'Expected Z3 version >= {version}, but z3 --version returned the following:')
    for line in lines:
      print_error('  ' + line)
    print_error_Exit('Get a recent Z3 executable from https://github.com/FStarLang/binaries/tree/master/z3-tested, modify .fstar_z3_version, or use the --FSTAR-Z3-MY-VERSION option to override')

def print_dump_args():
  print('Currently using the following F* args:')
  fstar_includes = compute_includes(src_include_paths, obj_include_paths, 'obj')
  for option in [fstar_z3_path, fstar_no_verify, fstar_includes, fstar_user_args, fstar_default_args]:
    if len(option) > 0:
      print(f'{option} ', end='')
  print()
  Exit(1)

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
  import time
  from SCons.Script import GetBuildFailures
  bf = GetBuildFailures()
  if bf:
    # bf is normally a list of build failures; if an element is None,
    # it's because of a target that scons doesn't know anything about.
    for x in bf:
      if x is not None:
        filename = bf_to_filename(x)
        if filename.endswith('.tmp') and os.path.isfile(filename):
          error_filename = filename[:-len('.tmp')] + '.error'
          stderr_filename = filename[:-len('.tmp')] + '.stderr'
          if os.path.isfile(error_filename):
            os.remove(error_filename)
          report_filename = stderr_filename if os.path.isfile(stderr_filename) else filename
          print()
          print(f'##### {red}Verification error{uncolor}')
          print('Printing contents of ' + report_filename + ' #####')
          with open (report_filename, 'r') as myfile:
            lines = myfile.read().splitlines()
            valeErrors = [line for line in lines if ("*****" in line)]
            for line in lines:
              if 'error was reported' in line or '(Error)' in line or ' failed' in line:
                line = f'{red}{line}{uncolor}'
              print(line)
          print()
          time.sleep(1)
          os.rename(filename, error_filename)

##################################################################################################
#
#   File and module processing functions
#
##################################################################################################

def add_module_for_file(file):
  global all_modules
  m = file_module_name(file)
  if m in all_modules:
    print(f'error: found more than one instance of module {m} (all module names must be unique for include paths to work correctly)')
    Exit(1)
  all_modules.append(m)

def add_include_dir_for_file(include_paths, file):
  d = str(file.dir)
  if not (d in include_paths):
    include_paths.append(d)
    distutils.dir_util.mkpath(str(to_obj_dir(file).dir))

def include_fstar_file(env, file):
  options = get_build_options(file)
  add_include_dir_for_file(src_include_paths, file)
  if options != None:
    if (file_extension(file) == ".fst"):
      add_module_for_file(file)
    fsti_map[file_module_name(file)] = file

def include_vale_file(env, file):
  options = get_build_options(file)
  add_include_dir_for_file(obj_include_paths, file)
  dummy_dir = File(f'obj/dummies/{file_drop_extension(file)}').dir
  distutils.dir_util.mkpath(str(dummy_dir))
  if options != None:
    add_module_for_file(file)
    module_name = file_module_name(file)
    fsti_map[module_name] = f'{file_drop_extension(to_obj_dir(file))}.fsti'
    for extension in ['.fst', '.fsti']:
      # The F* dependency analysis runs before .vaf files are converted to .fst/.fsti files,
      # so generate a dummy .fst/.fsti file pair for each .vaf file for the F* dependency analysis.
      dummy_file = File(f'obj/dummies/{file_drop_extension(file)}{extension}')
      distutils.dir_util.mkpath(str(dummy_file.dir))
      with open(str(dummy_file), 'w') as myfile:
        myfile.write(f'module {module_name}' + '\n')

def add_ml_dependencies(targets, sources):
  if fstar_extract:
    sources_ml = [ml_out_file(File(x), '.ml') for x in sources if is_our_file(File(x))]
    targets_ml = [ml_out_file(File(x), '.ml') for x in targets if is_our_file(File(x))]
    sources_ml = [x for x in sources_ml if not (x in no_extraction_files)]
    targets_ml = [x for x in targets_ml if not (x in no_extraction_files)]
    sources_ml = [x for x in sources_ml if not (x in targets_ml)]
    Depends(targets_ml, sources_ml)
    for t in targets_ml:
      if not (t in ml_out_deps):
        ml_out_deps[t] = set()
      for s in sources_ml:
        ml_out_deps[t].add(s)

# Verify a .fst or .fsti file
def verify_fstar_file(options, targetfile, sourcefile, fstar_includes):
  env = options.env
  stderrfile = File(f'{targetfile}.stderr')
  temptargetfile = File(f'{targetfile}.tmp')
  temptargetfiles = [temptargetfile]
  hintfile = to_hint_file(sourcefile)
  outs = []
  if min_test and on_black_list(sourcefile, min_test_suite_blacklist):
    print(f'Skipping {sourcefile} because it is on the min_test_suite_blacklist defined in SConscript')
    return outs
  if record_hints:
    temptargetfiles.append(hintfile)
  elif use_hints and os.path.isfile(str(hintfile)):
    Depends(temptargetfiles, hintfile)
  temptargets = env.Command(temptargetfiles, sourcefile,
    f'{fstar_exe} {sourcefile} {options.verifier_flags} {fstar_z3_path} {fstar_no_verify}' +
    f' {fstar_includes} {" ".join(fstar_user_args)} --hint_file {hintfile}' +
    f' 1> {temptargetfile} 2> {stderrfile}')
  temptarget = temptargets[0]
  outs.append(CopyFile(targetfile, temptarget))
  return outs

def extract_fstar_file(options, sourcefile, fstar_includes):
  env = options.env
  base_name = file_drop_extension(sourcefile)
  module_name = file_module_name(sourcefile)
  hintfile = to_hint_file(sourcefile)
  mlfile = ml_out_file(sourcefile, '.ml')
  Depends(mlfile, to_obj_dir(base_name + '.fst.verified'))
  verifier_flags = options.verifier_flags.replace('--use_extracted_interfaces true', '')
  return env.Command(mlfile, sourcefile,
    f'{fstar_exe} {sourcefile} {verifier_flags} {fstar_z3_path} {fstar_no_verify}' +
    f' {fstar_includes} {" ".join(fstar_user_args)} --hint_file {hintfile}' +
    f' --odir obj/ml_out --codegen OCaml --admit_smt_queries true --extract_module {module_name}')

# Process a .fst or .fsti file
def process_fstar_file(env, file, fstar_includes):
  options = get_build_options(file)
  if options != None:
    if verify:
      target = File(f'{to_obj_dir(file)}.verified')
      verify_fstar_file(options, target, file, fstar_includes)
      if fstar_extract:
        if file_extension(file) == '.fst':
          if not (ml_out_file(file, '.ml') in no_extraction_files):
            extract_fstar_file(options, file, fstar_includes)

def vale_dependency_scan(env, file):
  contents = file.get_text_contents()
  dirname = os.path.dirname(str(file))
  vaf_includes = vale_include_re.findall(contents)
  fst_includes = vale_open_re.findall(contents) + vale_import_re.findall(contents)
  obj_file_base = file_drop_extension(to_obj_dir(file))
  obj_tmps = [f'{obj_file_base}.fst.verified.tmp', f'{obj_file_base}.fsti.verified.tmp']
  for (attrs, inc) in vaf_includes:
    f = os.path.join('code' if vale_from_base_re.search(attrs) else dirname, inc)
    # if A.vaf includes B.vaf, then manually establish these dependencies:
    #   A.fst.verified  depends on B.fsti
    #   A.fsti.verified depends on B.fsti
    f_base = file_drop_extension(to_obj_dir(File(f)))
    f_fsti = File(f_base + '.fsti.verified')
    Depends(obj_tmps, f_fsti)
    add_ml_dependencies([obj_file_base + '.fst'], [f_base + '.fst'])
  for inc in fst_includes:
    if inc in fsti_map:
      Depends(obj_tmps, [fsti_map[inc]])
      add_ml_dependencies([obj_file_base + '.fst'], [fsti_map[inc]])

# Translate Vale .vaf to F* .fst/fsti pair
# Takes a source .vaf File node
# Returns list of File nodes representing the resulting .fst and .fsti files
def translate_vale_file(options, source_vaf):
  env = options.env
  target = file_drop_extension(to_obj_dir(source_vaf))
  target_fst = File(target + '.fst')
  target_fsti = File(target + '.fsti')
  targets = [target_fst, target_fsti]
  opt_vale_includes = vale_includes if options.vale_includes == None else options.vale_includes
  env.Command(targets, source_vaf,
    f'{mono} {vale_exe} -fstarText {opt_vale_includes}' +
    f' -in {source_vaf} -out {target_fst} -outi {target_fsti}' +
    f' {vale_scons_args} {" ".join(vale_user_args)}')
  return targets

# Process a .vaf file
def process_vale_file(env, file, fstar_includes):
  options = get_build_options(file)
  if options != None:
    vale_dependency_scan(env, file)
    fsts = translate_vale_file(options, file)
    fst = fsts[0]
    fsti = fsts[1]
    if verify:
      fst_options = get_build_options(fst)
      fsti_options = get_build_options(fsti)
      target = file_drop_extension(to_obj_dir(file))
      target_fst = f'{target}.fst.verified'
      target_fsti = f'{target}.fsti.verified'
      verify_fstar_file(fst_options, target_fst, fst, fstar_includes)
      verify_fstar_file(fsti_options, target_fsti, fsti, fstar_includes)
      if fstar_extract:
        extract_fstar_file(fst_options, fst, fstar_includes)

def recursive_glob(env, pattern, strings = False):
  matches = []
  split = os.path.split(pattern) # [0] is the directory, [1] is the actual pattern
  platform_directory = split[0] #os.path.normpath(split[0])
  for d in os.listdir(platform_directory):
    if os.path.isdir(os.path.join(platform_directory, d)):
      newpattern = os.path.join(split[0], d, split[1])
      matches.append(recursive_glob(env, newpattern, strings))
  files = env.Glob(pattern, strings=strings)
  matches.append(files)
  return Flatten([File(x) for x in matches])

# Verify *.fst, *.fsti, *.vaf files in a list of directories.  This enumerates
# all files in those trees, and creates verification targets for each,
# which in turn causes a dependency scan to verify all of their dependencies.
def process_files_in(env, directories):
  fsts = []
  fstis = []
  vafs = []
  for d in directories:
    fsts.extend(recursive_glob(env, d + '/*.fst', strings = True))
    fstis.extend(recursive_glob(env, d + '/*.fsti', strings = True))
    vafs.extend(recursive_glob(env, d + '/*.vaf', strings = True))
  # Compute include directories:
  for file in fsts:
    include_fstar_file(env, file)
  for file in fstis:
    include_fstar_file(env, file)
  for file in vafs:
    include_vale_file(env, file)
  # Process and verify files:
  fstar_include_paths = compute_include_paths(src_include_paths, obj_include_paths, 'obj')
  fstar_includes = compute_includes(src_include_paths, obj_include_paths, 'obj')
  if is_single_vaf:
    process_vale_file(env, single_vaf, fstar_includes)
  else:
    for file in fsts:
      process_fstar_file(env, file, fstar_includes)
    for file in fstis:
      process_fstar_file(env, file, fstar_includes)
    for file in external_files:
      process_fstar_file(env, File(file), fstar_includes)
    for file in vafs:
      process_vale_file(env, file, fstar_includes)

def extract_assembly_code(env, output_base_name, main_file, alg_file, cmdline_file):
  # OCaml depends on many libraries and executables; we have to assume they are in the user's PATH:
  ocaml_env = Environment(ENV = {'PATH' : os.environ['PATH'], 'OCAMLPATH' : fstar_path + '/bin'})
  main_ml = ml_out_file(main_file, '.ml')
  main_cmx = ml_out_file(main_file, '.cmx')
  main_exe = ml_out_file(main_file, '.exe')
  alg_ml = ml_out_file(alg_file, '.ml')
  alg_cmx = ml_out_file(alg_file, '.cmx')
  cmdline_ml = ml_out_file(cmdline_file, '.ml')
  cmdline_cmx = ml_out_file(cmdline_file, '.cmx')
  pointer_src = File('code/lib/util/FStar_Pointer_Base.ml')
  pointer_ml = ml_out_file(pointer_src, '.ml')
  pointer_cmx = ml_out_file(pointer_src, '.cmx')
  CopyFile(pointer_ml, pointer_src)
  CopyFile(cmdline_ml, cmdline_file)
  CopyFile(main_ml, main_file)
  Depends(cmdline_cmx, alg_cmx)
  Depends(cmdline_cmx, cmdline_ml)
  Depends(main_cmx, alg_cmx)
  Depends(main_cmx, cmdline_cmx)
  Depends(main_cmx, main_ml)
  done = set()
  cmxs = []
  def add_cmx(x_ml):
    x_cmx = ml_out_file(x_ml, '.cmx')
    if x_ml != pointer_ml:
      Depends(x_cmx, pointer_cmx)
    cmx = ocaml_env.Command(x_cmx, x_ml,
      f'ocamlfind ocamlopt -c -package fstarlib -package fstar-tactics-lib -o {x_cmx} {x_ml} -I obj/ml_out')
    cmxs.append(cmx[0])
    Depends(main_exe, cmx[0])
  def collect_cmxs_in_order(x_ml):
    if not (x_ml in done):
      done.add(x_ml)
      for y_ml in sorted(ml_out_deps[x_ml]): # sorting makes the order deterministic, so scons doesn't needlessly rebuild
        # if x depends on y, y must appear first in ocaml link step
        Depends(ml_out_file(x_ml, '.cmx'), ml_out_file(y_ml, '.cmx'))
        collect_cmxs_in_order(y_ml)
      Depends(x_ml, pointer_ml)
      add_cmx(x_ml)
  add_cmx(pointer_ml)
  collect_cmxs_in_order(alg_ml)
  add_cmx(cmdline_ml)
  add_cmx(main_ml)
  cmxs_string = " ".join([str(cmx) for cmx in cmxs])
  ocaml_env.Command(main_exe, cmxs,
    f'ocamlfind ocamlopt -linkpkg -package fstarlib -package fstar-tactics-lib {cmxs_string} -o {main_exe}')
  # Run executable to generate assembly files:
  output_target_base = 'obj/' + output_base_name
  def generate_asm(suffix, assembler, platform):
    target = output_target_base + suffix
    return env.Command(target, main_exe, f'{main_exe} {assembler} {platform} > {target}')
  masm_win = generate_asm('.asm', 'MASM', 'Win')
  gcc_win = generate_asm('-gcc.S', 'GCC', 'Win')
  gcc_linux = generate_asm('-linux.S', 'GCC', 'Linux')
  gcc_macos = generate_asm('-macos.S', 'GCC', 'MacOS')
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

##################################################################################################
#
#   FStar dependency analysis
#
##################################################################################################

def compute_fstar_deps(env, src_directories, fstar_includes):
  import subprocess
  # find all .fst, .fsti files in src_directories
  fst_files = []
  for d in src_directories:
    fst_files.extend(recursive_glob(env, d+'/*.fst', strings = True))
    fst_files.extend(recursive_glob(env, d+'/*.fsti', strings = True))
  # use fst_files to choose .fst and .fsti files that need dependency analysis
  files = []
  for f in fst_files:
    options = get_build_options(f)
    if options != None:
      files.append(f)
  # call fstar --dep make
  includes = []
  for include in fstar_includes:
    includes += ["--include", include]
  lines = []
  depsBackupFile = 'obj/fstarDepsBackup.d'
  args = ["--dep", "make"] + includes + files
  cmd = [fstar_exe] + args
  cmd = [str(x) for x in cmd]
  #print(" ".join(cmd))
  try:
    print('F* dependency analysis starting')
    o = subprocess.check_output(cmd, stderr = subprocess.STDOUT).decode('ascii')
    print('F* dependency analysis finished')
  except (subprocess.CalledProcessError) as e:
    print(f'F* dependency analysis: error: {e.output}')
    Exit(1)
  fstar_deps_ok = True
  lines = o.splitlines()
  for line in lines:
    if 'Warning:' in line:
      print(line)
      fstar_deps_ok = False
    if len(line) == 0:
      pass
    else:
      # lines are of the form:
      #   a1.fst a2.fst ... : b1.fst b2.fst ...
      # we change this to:
      #   obj\...\a1.fst.verified obj\...\a2.fst.verified ... : b1.fst.verified b2.fst.verified ...
      # we ignore targets that we will not verify (e.g. F* standard libraries)
      targets, sources = line.split(': ', 1) # ': ', not ':', because of Windows drive letters
      sources = sources.split()
      targets = targets.split()
      obj_name = str(Dir('obj'))
      dummies_name = str(Dir('obj/dummies'))
      sources = [str(File(x)).replace(dummies_name, obj_name) for x in sources]
      targets = [str(File(x)).replace(dummies_name, obj_name) for x in targets]
      for source in sources:
        for target in targets:
          if target.startswith('specs') and (source.startswith('obj') or source.startswith('code')):
            print(f'{yellow}Warning: file {target} in specs directory depends on file {source} outside specs directory{uncolor}')
      sources_ver = [to_obj_dir(File(re.sub('\.fst$', '.fst.verified', re.sub('\.fsti$', '.fsti.verified', x)))) for x in sources if is_our_file(File(x))]
      targets_ver = [to_obj_dir(File(re.sub('\.fst$', '.fst.verified.tmp', re.sub('\.fsti$', '.fsti.verified.tmp', x)))) for x in targets if is_our_file(File(x))]
      Depends(targets_ver, sources_ver)
      add_ml_dependencies(targets, sources)
  if fstar_deps_ok:
    # Save results in depsBackupFile
    with open(depsBackupFile, 'w') as myfile:
      for line in lines:
        myfile.write(line + '\n')
  else:
    print('F* dependency analysis failed')
    Exit(1)

##################################################################################################
#
#   Top-level commands
#
##################################################################################################

atexit.register(report_verification_failures)
env = common_env

# Create obj directory and any subdirectories needed during dependency analysis
# (SCons will create other subdirectories during build)
distutils.dir_util.mkpath('obj')
distutils.dir_util.mkpath('obj/external')
distutils.dir_util.mkpath('obj/cache_checked')

# Check F* and Z3 versions
if not fstar_my_version:
  check_fstar_version()
if verify and not fstar_z3_my_version:
  if not found_z3:
    print_error_exit('Could not find z3 executable.  Either put z3 in your path, or put it in the directory tools/Z3/, or use the --FSTARZ3=<z3-executable> option.')
  check_z3_version(fstar_z3)

# HACK: copy external files
for x in ['CanonCommSwaps.fst', 'CanonCommMonoid.fst', 'CanonCommSemiring.fst']:
  source = f'{fstar_path}/examples/tactics/{x}'
  target = f'obj/external/{x}'
  shutil.copy(source, target)
for x in ['C.Loops.fst', 'Spec.Loops.fst']:
  source = f'{kremlin_path}/kremlib/{x}'
  target = f'obj/external/{x}'
  shutil.copy(source, target)

print('Processing source files')
process_files_in(env, verify_paths)
compute_fstar_deps(env, verify_paths, compute_include_paths(src_include_paths, obj_include_paths, 'obj/dummies'))

if fstar_extract:
  # Build AES-GCM
  aesgcm_asm = extract_assembly_code(env, 'aesgcm', File('code/crypto/aes/x64/Main.ml'),
    File('code/crypto/aes/x64/X64.GCMdecrypt.vaf'), File('code/lib/util/CmdLineParser.ml'))
  if env['TARGET_ARCH'] == 'amd64':
    aesgcmasm_obj = env.Object('obj/aesgcmasm_openssl', aesgcm_asm[0])
    aesgcmtest_src = File('code/crypto/aes/x64/TestAesGcm.cpp')
    aesgcmtest_cpp = to_obj_dir(aesgcmtest_src)
    CopyFile(aesgcmtest_cpp, aesgcmtest_src)
    aesgcmtest_exe = env.Program(source = [aesgcmasm_obj, aesgcmtest_cpp], target = 'obj/TestAesGcm.exe')

if dump_args:
  print_dump_args()
