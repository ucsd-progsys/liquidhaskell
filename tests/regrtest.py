#!/usr/bin/python
# Copyright (c) 2009 The Regents of the University of California. All rights reserved.
#
# Permission is hereby granted, without written agreement and without
# license or royalty fees, to use, copy, modify, and distribute this
# software and its documentation for any purpose, provided that the
# above copyright notice and the following two paragraphs appear in
# all copies of this software.
#
# IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO ANY PARTY
# FOR DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES
# ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN
# IF THE UNIVERSITY OF CALIFORNIA HAS BEEN ADVISED OF THE POSSIBILITY
# OF SUCH DAMAGE.
#
# THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY WARRANTIES,
# INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY
# AND FITNESS FOR A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED HEREUNDER IS
# ON AN "AS IS" BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION
# TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.

import time, subprocess, optparse, sys, socket, os
sys.path.append("../")
import rtest as rtest

solve         = "liquid ".split()
null          = open("/dev/null", "w")
now	          = (time.asctime(time.localtime(time.time()))).replace(" ","_")
logfile       = "../tests/logs/regrtest_results_%s_%s" % (socket.gethostname (), now)
argcomment    = "--! run with "
liquidcomment = "{--! run liquid with "
endcomment    = "-}"

def logged_sys_call(args, out=None, err=None, dir=None):
  print "exec: " + " ".join(args)
  return subprocess.call(args, stdout=out, stderr=err, cwd=dir)
 
def solve_quals(dir,file,bare,time,quiet,flags,lflags):
  if quiet: out = null
  else: out = None
  if time: time = ["time"]
  else: time = []
  if lflags: lflags = ["--" + f for f in lflags]
  hygiene_flags = []
  (dn, bn) = os.path.split(file)
  try:
    os.makedirs(os.path.join(dir,dn,".liquid"))
  except OSError:
    pass
  out = open(os.path.join(dir,dn,".liquid",bn) + ".log", "w")
  rv  = logged_sys_call(time + solve + flags + lflags + hygiene_flags + [file],
                        out=None, err=subprocess.STDOUT, dir=dir)
  out.close()
  return rv

def run_script(file,quiet):
  if quiet: out = null
  else: out = None
  return logged_sys_call(file, out)

def getfileargs(file):
  f = open(file)
  l = f.readline()
  f.close()
  if l.startswith(argcomment):
    return l[len(argcomment):].strip().split(" ")
  else:
    return []

def getliquidargs(file):
  f = open(file)
  l = f.readline()
  f.close()
  if l.startswith(liquidcomment):
    return [arg for arg in l[len(liquidcomment):].strip().split(" ")
                     if arg!=endcomment]
  else:
    return []


class Config (rtest.TestConfig):
  def __init__ (self, dargs, testdirs, logfile, threadcount):
    rtest.TestConfig.__init__ (self, testdirs, logfile, threadcount)
    self.dargs = dargs

  def run_test (self, dir, file):
    path = os.path.join(dir,file)
    if self.is_test(file):
      lflags = getliquidargs(path)
      fargs  = getfileargs(path)
      fargs  = self.dargs + fargs  
      return solve_quals(dir, file, True, False, True, fargs, lflags)
    elif file.endswith(".sh"):
      return run_script(path, True)

  def is_test (self, file):
    return file.endswith(".hs") # or file.endswith(".lhs")

#####################################################################################

#DEFAULT

textIgnored = { "Data/Text/Axioms.hs"
              , "Data/Text/Encoding/Error.hs"
              , "Data/Text/Encoding/Fusion.hs"
              , "Data/Text/Encoding/Fusion/Common.hs"
              , "Data/Text/Encoding/Utf16.hs"
              , "Data/Text/Encoding/Utf32.hs"
              , "Data/Text/Encoding/Utf8.hs"
              , "Data/Text/Fusion/CaseMapping.hs"
              , "Data/Text/Fusion/Common.hs"
              , "Data/Text/Fusion/Internal.hs"
              , "Data/Text/IO.hs"
              , "Data/Text/IO/Internal.hs"
              , "Data/Text/Lazy/Builder/Functions.hs"
              , "Data/Text/Lazy/Builder/Int.hs"
              , "Data/Text/Lazy/Builder/Int/Digits.hs"
              , "Data/Text/Lazy/Builder/Internal.hs"
              , "Data/Text/Lazy/Builder/RealFloat.hs"
              , "Data/Text/Lazy/Builder/RealFloat/Functions.hs"
              , "Data/Text/Lazy/Encoding/Fusion.hs"
              , "Data/Text/Lazy/IO.hs"
              , "Data/Text/Lazy/Read.hs"
              , "Data/Text/Read.hs"
              , "Data/Text/Unsafe/Base.hs"
              , "Data/Text/UnsafeShift.hs"
              , "Data/Text/Util.hs"
              }

demosIgnored = { "Composition.hs"
               , "Eval.hs"
               , "Inductive.hs"
               , "Loop.hs"
               , "TalkingAboutSets.hs"
               , "refinements101reax.hs"
               }

regtestdirs  = [ ("pos", {}, 0)
               , ("neg", {}, 1)
               , ("crash", {}, 2)
               , ("parser/pos", {}, 0)
               , ("error_messages/pos", {}, 0)
               , ("error_messages/crash", {}, 2)
               ]

benchtestdirs = [ ("../web/demos", demosIgnored, 0)
                , ("../benchmarks/esop2013-submission", {"Base0.hs"}, 0)
                , ("../benchmarks/bytestring-0.9.2.1", {}, 0)
                , ("../benchmarks/text-0.11.2.3", textIgnored, 0)
                , ("../benchmarks/vector-algorithms-0.5.4.2", {}, 0)
                , ("../benchmarks/hscolour-1.20.0.0", {}, 0)
                ]

parser = optparse.OptionParser()
parser.add_option("-a", "--all", action="store_true", dest="alltests", help="run all tests")
parser.add_option("-t", "--threads", dest="threadcount", default=1, type=int, help="spawn n threads")
parser.add_option("-o", "--opts", dest="opts", default=[], action='append', type=str, help="additional arguments to liquid")
parser.disable_interspersed_args()
options, args = parser.parse_args()

print "options =", options
print "args =", args

def testdirs():
  global testdirs
  if options.alltests:
    return regtestdirs + benchtestdirs
  else:
    return regtestdirs

testdirs = testdirs()

clean = os.path.abspath("../cleanup")
[os.system(("cd %s; %s; cd ../" % (d,clean))) for (d,_,_) in testdirs]
runner = rtest.TestRunner (Config (options.opts, testdirs, logfile, options.threadcount))
sys.exit(runner.run())
