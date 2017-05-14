#!/usr/bin/python

from collections import defaultdict
from datetime import datetime
import os
import re
import string
import subprocess

benchmarks = {
'benchmarks/icfp17/applicative' : [
 'ApplicativeId.hs'
, 'ApplicativeMaybe.hs'
, 'ApplicativeReader.hs'
],
'benchmarks/icfp17/arith' : [
 'Ackermann.hs'
, 'Fibonacci.hs'
],
'benchmarks/icfp17/data-structs' : [
 'Array.hs'
, 'Base.hs'
, 'Fib.hs'
, 'GhcListSort.hs'
, 'ListSort.hs'
, 'RBTree.hs'
, 'Splay.hs'
, 'Toy.hs'
],
'benchmarks/icfp17/monad' : [
 'MonadId.hs'
, 'MonadList.hs'
, 'MonadMaybe.hs'
, 'MonadReader.hs'
],
'benchmarks/icfp17/text-0.11.2.3' : [
 'Data/Text/Array.hs'
, 'Data/Text/Encoding.hs'
, 'Data/Text/Foreign.hs'
, 'Data/Text/Fusion/Size.hs'
, 'Data/Text/Fusion.hs'
, 'Data/Text/Internal.hs'
, 'Data/Text/Lazy/Builder.hs'
, 'Data/Text/Lazy/Encoding.hs'
, 'Data/Text/Lazy/Fusion.hs'
, 'Data/Text/Lazy/Internal.hs'
, 'Data/Text/Lazy/Search.hs'
, 'Data/Text/Lazy.hs'
, 'Data/Text/Private.hs'
, 'Data/Text/Search.hs'
, 'Data/Text/Unsafe.hs'
, 'Data/Text/UnsafeChar.hs'
, 'Data/Text.hs'
# , 'Setup.lhs'
],
'benchmarks/icfp17/functor' : [
 'FunctorId.hs'
, 'FunctorList.hs'
, 'FunctorMaybe.hs'
, 'FunctorReader.hs'
, 'FunctorReader.NoExtensionality.hs'
],
'benchmarks/icfp17/fold' : [
 'FoldrUniversal.hs'
],
'benchmarks/icfp17/vector-algorithms-0.5.4.2' : [
 'Data/Vector/Algorithms/AmericanFlag.hs'
, 'Data/Vector/Algorithms/Combinators.hs'
, 'Data/Vector/Algorithms/Common.hs'
, 'Data/Vector/Algorithms/Heap.hs'
, 'Data/Vector/Algorithms/Insertion.hs'
, 'Data/Vector/Algorithms/Intro.hs'
, 'Data/Vector/Algorithms/Merge.hs'
, 'Data/Vector/Algorithms/Optimal.hs'
, 'Data/Vector/Algorithms/Radix.hs'
, 'Data/Vector/Algorithms/Search.hs'
, 'Data/Vector/Algorithms/Termination.hs'
# , 'Setup.lhs'
],
'benchmarks/icfp17/unification' : [
 'Unification.hs'
],
'benchmarks/icfp17/sat-solver' : [
 'Solver.hs'
],
'benchmarks/icfp17/bytestring-0.9.2.1' : [
 'Data/ByteString/Char8.hs'
, 'Data/ByteString/Fusion.hs'
, 'Data/ByteString/Fusion.T.hs'
, 'Data/ByteString/Internal.hs'
, 'Data/ByteString/Lazy/Char8.hs'
, 'Data/ByteString/Lazy/Internal.hs'
, 'Data/ByteString/Lazy.hs'
, 'Data/ByteString/LazyZip.hs'
, 'Data/ByteString/Unsafe.hs'
, 'Data/ByteString.hs'
, 'Data/ByteString.T.hs'
],
'benchmarks/icfp17/monoid' : [
 'MonoidList.hs'
, 'MonoidMaybe.hs'
],
}

benchmarksNames = {
'benchmarks/icfp17/data-structs' : "DATA-STRUCT",
'benchmarks/icfp17/vector-algorithms-0.5.4.2' : "VEC-ALGOS",
'benchmarks/icfp17/bytestring-0.9.2.1' : "BYTESTRING",
'benchmarks/icfp17/text-0.11.2.3' : "TEXT",
'benchmarks/icfp17/arith' : "ARITH",
'benchmarks/icfp17/fold' : "FOLD",
'benchmarks/icfp17/monoid' : "MONOID",
'benchmarks/icfp17/functor' : "FUNCTOR",
'benchmarks/icfp17/applicative' : "APPLICATIVE",
'benchmarks/icfp17/monad' : "MONAD",
'benchmarks/icfp17/sat-solver' : "SAT-SOLVER",
'benchmarks/icfp17/unification' : "UNIFICATION",
}

benchmarksOrdered = [
'benchmarks/icfp17/data-structs',
'benchmarks/icfp17/vector-algorithms-0.5.4.2',
'benchmarks/icfp17/bytestring-0.9.2.1',
'benchmarks/icfp17/text-0.11.2.3',
'benchmarks/icfp17/arith',
'benchmarks/icfp17/fold',
'benchmarks/icfp17/monoid',
'benchmarks/icfp17/functor',
'benchmarks/icfp17/applicative',
'benchmarks/icfp17/monad',
'benchmarks/icfp17/sat-solver',
'benchmarks/icfp17/unification',
]

def sloc(scripts,fn):
    out = subprocess.check_output('sloccount %s 2> /dev/null' % fn, shell=True)
    return int(out.split('haskell=')[1].split(',')[0].split('\n')[0])

def lines(anns):
    return sum(map(lambda x:(1+x.count('\n')), anns))

def find(rx, str):
    return [(str[a.start():(3+string.find(str,"@-}", a.start()))])
            for a in list(re.finditer(rx, str))]

other = 'import|include|invariant|embed|Decrease|LAZYVAR|Strict|Lazy'
other_re = '{-@ (%s)' % other
spec_re = '{-@ (?!(%s|qualif|LIQUID))' % other

def combine(x, y):
    return {k:x[k] + y[k] for k in y.keys()}

def csvify(fn, metrics):
    return '%s, %d, %d, %d\n' % (
        fn, metrics['sloc'], metrics['specs_lines'] +
        metrics['others_lines'], int(metrics['time']))

def mkTimeDict(timeFile):
    times = timeFile.readlines()
    times = [line.split(',') for line in times if "True\n" in line]
    timeDict = {}
    for time in times:
        timeDict[time[0]] = float(time[1])
    return timeDict

def main():
    subprocess.call('stack test liquidhaskell', shell=True)
    subprocess.call('mv tests/logs/cur/summary.csv tests/logs/cur/summary-FUSION.csv', shell=True)
    with open('tests/logs/cur/summary-FUSION.csv', 'r') as timeFile:
        timeDictF = mkTimeDict(timeFile)

    # subprocess.call('stack test liquidhaskell', shell=True)
    # subprocess.call('mv tests/logs/cur/summary.csv tests/logs/cur/summary-LIQUID.csv', shell=True)
    # with open('tests/logs/cur/summary-LIQUID.csv', 'r') as timeFile:
    #     timeDictF = mkTimeDict(timeFile)

    results = {}
    pwd = os.getcwd()
    for d, fs in benchmarks.iteritems():
        os.chdir(d)
        results[d] = {}
        for fn in fs:
            print fn
            f_res = {}
            f_res['sloc'] = sloc(os.path.join(pwd,'scripts'),fn)

            f_res['time'] = timeDictF["Tests/Benchmarks/%s/%s" % (benchmarksNames[d], fn)]

            str = (open(fn, 'r')).read()

            specs = find(spec_re, str)
            f_res['specs_lines'] = lines(specs)

            others = find(other_re, str)
            f_res['others_lines'] = lines(others)

            results[d][fn] = f_res

        os.chdir(pwd)

    with open('metrics.csv', 'w') as out:
        for d in benchmarksOrdered:
            fs = results[d]
            dirtotals = defaultdict(int)
            for fn, metrics in sorted(fs.iteritems()):
                dirtotals = combine(dirtotals, metrics)
            displayName = benchmarksNames[d]
            out.write(csvify(displayName, dirtotals))

if __name__ == '__main__':
    main()
