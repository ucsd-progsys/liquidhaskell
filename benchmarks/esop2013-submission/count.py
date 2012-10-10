#!/usr/bin/python

# used by count.sh

import re
import sys
import string

fname = sys.argv[1]
str = (open(fname, 'r')).read()

measures =   [(str[a.start():(3+string.find(str,"@-}", a.start()))]) for a in list(re.finditer('{-@ measure', str)) ]
tydefs =   [(str[a.start():(3+string.find(str,"@-}", a.start()))]) for a in list(re.finditer('{-@ type', str)) ]
annotations =   [(str[a.start():(3+string.find(str,"@-}", a.start()))]) for a in list(re.finditer('{-@ (?!(type|measure))', str)) ]

#print measures
#print tydefs
#print annotations
print "Measures        :\t\t count = %d \t chars = %d \t lines = %d"  %(len(measures), sum(map(lambda x:len(x), measures)), sum(map(lambda x:(1+x.count('\n')), measures)))
print "Type definitions:\t\t count = %d \t chars = %d \t lines = %d" %(len(tydefs), sum(map(lambda x:len(x), tydefs)), sum(map(lambda x:(1+x.count('\n')), tydefs)))
print "Annotations     :\t\t count = %d \t chars = %d \t lines = %d" %(len(annotations), sum(map(lambda x:len(x), annotations)), sum(map(lambda x:(1+x.count('\n')), annotations)))

