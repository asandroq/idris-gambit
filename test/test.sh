#!/bin/bash

set -e

BASE=$1

stack build --fast --haddock
stack exec idris -- --codegen gambit -o "${BASE}.scm" "${BASE}.idr"
gsi -e "(pretty-print (with-input-from-file \"${BASE}.scm\" read-all))" > "${BASE}2.scm"
gsi "${BASE}.scm"
