#!/bin/sh

./bench-cmp.pl "$@" | column -nts\; | less -SR
