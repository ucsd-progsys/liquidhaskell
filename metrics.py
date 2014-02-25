#!/usr/bin/python

from collections import defaultdict
from datetime import datetime
import os
import re
import string
import subprocess
import sys

benchmarks = {
    'benchmarks/text-0.11.2.3': [ 'Data/Text.hs'
                                , 'Data/Text/Array.hs'
                                , 'Data/Text/Encoding.hs'
                                , 'Data/Text/Foreign.hs'
                                , 'Data/Text/Fusion.hs'
                                , 'Data/Text/Fusion/Size.hs'
                                , 'Data/Text/Internal.hs'
                                , 'Data/Text/Lazy.hs'
                                , 'Data/Text/Lazy/Builder.hs'
                                , 'Data/Text/Lazy/Encoding.hs'
                                , 'Data/Text/Lazy/Fusion.hs'
                                , 'Data/Text/Lazy/Internal.hs'
                                , 'Data/Text/Lazy/Search.hs'
                                , 'Data/Text/Private.hs'
                                , 'Data/Text/Search.hs'
                                , 'Data/Text/Unsafe.hs'
                                , 'Data/Text/UnsafeChar.hs' ],

    'benchmarks/bytestring-0.9.2.1': [ 'Data/ByteString.T.hs'
                                     , 'Data/ByteString/Char8.hs'
                                     , 'Data/ByteString/Fusion.T.hs'
                                     , 'Data/ByteString/Internal.hs'
                                     , 'Data/ByteString/Lazy.hs'
                                     # , 'Data/ByteString/LazyZip.hs'
                                     , 'Data/ByteString/Lazy/Char8.hs'
                                     , 'Data/ByteString/Lazy/Internal.hs'
                                     , 'Data/ByteString/Unsafe.hs' ],

    'benchmarks/vector-algorithms-0.5.4.2': [ 'Data/Vector/Algorithms/AmericanFlag.hs'
                                            , 'Data/Vector/Algorithms/Combinators.hs'
                                            , 'Data/Vector/Algorithms/Common.hs'
                                            , 'Data/Vector/Algorithms/Heap.hs'
                                            , 'Data/Vector/Algorithms/Insertion.hs'
                                            , 'Data/Vector/Algorithms/Intro.hs'
                                            , 'Data/Vector/Algorithms/Merge.hs'
                                            , 'Data/Vector/Algorithms/Optimal.hs'
                                            , 'Data/Vector/Algorithms/Radix.hs'
                                            , 'Data/Vector/Algorithms/Search.hs' ],

    'benchmarks/esop2013-submission': [ 'Base.hs', 'Splay.hs' ],

    'include': [ 'GHC/List.lhs' ],

    '.': [ 'benchmarks/base-4.5.1.0/Data/List.hs' ]
}

def time(fn):
    start = datetime.now()
    with open(fn+'.log', 'w') as out:
        subprocess.call(['liquid', '--smtsolver', 'z3mem', fn], stdout=out, stderr=out)
    return (datetime.now() - start).total_seconds()

def errors(fn):
    with open(fn+'.log') as fd:
        log = fd.readlines()
    unsafes = [l for l in log if l.startswith('**** UNSAFE:')]
    return unsafes

def sloc(fn):
    return int(subprocess.check_output('sloccount --details %s | grep -E "haskell\stop_dir" | cut -f1' % fn, shell=True))

def lines(anns):
    return sum(map(lambda x:(1+x.count('\n')), anns))

def recs(fn):
    out = subprocess.check_output('liquid-count-binders %s 2>/dev/null' % fn, shell=True)
    return [int(n) for n in re.findall('(\d+)', out)]

def find(rx, str):
    return [(str[a.start():(3+string.find(str,"@-}", a.start()))])
            for a in list(re.finditer(rx, str))]

qualif_re = '{-@ qualif'
other = 'import|include|invariant|embed|Decrease|LAZYVAR|Strict|Lazy'
other_re = '{-@ (%s)' % other
spec_re = '{-@ (?!(%s|qualif|LIQUID))' % other
dec_re = '{-@ Decrease'
term_re = '{-@ (Strict|Lazy)'
wit_re = '{- LIQUID WITNESS'
mod_re = '^module ([\w\.]+)'

def combine(x, y):
    return {k:x[k] + y[k] for k in y.keys()}

def texify(fn, metrics):
    return '\\texttt{%s} & %d & %d / %d & %d / %d & %d / %d & %d & %d & %d & %d & %d & %d & %d \\\\\n' % (
        fn, metrics['sloc'], metrics['specs'], metrics['specs_lines'],
        metrics['others'], metrics['others_lines'],
        metrics['qualifs'], metrics['qualifs_lines'],
        metrics['funs'], metrics['recs'], metrics['recfuns'], metrics['terms'],
        metrics['decs'], metrics['wits'], metrics['time'])

def main():
    results = {}
    pwd = os.getcwd()
    for d, fs in benchmarks.iteritems():
        os.chdir(d)
        results[d] = {}
        for fn in fs:
            print fn
            f_res = {}
            f_res['time'] = time(fn)
            f_res['sloc'] = sloc(fn)
            [fs,rs,rfs] = recs(fn)
            f_res['funs'] = fs
            f_res['recs'] = rs
            f_res['recfuns'] = rfs

            import pprint
            pprint.pprint(errors(fn))

            str = (open(fn, 'r')).read()
            mod = re.search(mod_re, str, re.M).group(1)

            specs = find(spec_re, str)
            f_res['specs'] = len(specs)
            f_res['specs_lines'] = lines(specs)

            qualifs = find(qualif_re, str)
            f_res['qualifs'] = len(qualifs)
            f_res['qualifs_lines'] = lines(qualifs)

            others = find(other_re, str)
            f_res['others'] = len(others)
            f_res['others_lines'] = lines(others)

            f_res['decs'] = len(re.findall(dec_re, str))
            f_res['terms'] = len(re.findall(term_re, str))
            f_res['wits'] = len(re.findall(wit_re, str))
            results[d][mod] = f_res

        os.chdir(pwd)

    with open('metrics.tex', 'w') as out:
        out.write('\\begin{tabular}{|l|rrrr|rrrrrr|r|}\n')
        out.write('\\hline\n')
        headers = ['Module', 'LOC', 'Specs', 'Annot', 'Qualif', 'Fun', 'Rec', 'RecFun', 'Serious', 'Hint', 'Wit', 'Time (s)']
        out.write(' & '.join('\\textbf{%s}' % h for h in headers) + '\\\\\n')
        out.write('\\hline\\hline\n')
        totals = defaultdict(int)
        for d, fs in results.iteritems():
            dirtotals = defaultdict(int)
            for fn, metrics in sorted(fs.iteritems()):
                out.write(texify(fn, metrics))
                dirtotals = combine(dirtotals, metrics)
            out.write(texify(d, dirtotals))
            out.write('\\hline\n\n')
            totals = combine(totals, dirtotals)
        out.write(texify('Total', totals))
        out.write('\\hline\n\\end{tabular}\n')

if __name__ == '__main__':
    main()
