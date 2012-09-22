#!/bin/bash

gcc -o test_capi -L../../lib -I../../include -lz3 test_capi.c
