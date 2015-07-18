#!/bin/bash
filename=$1
base=${filename%.*}
scriptdir=`dirname $0`
cc=$scriptdir/compiler
$cc < $1 > $base.ml
ocamlopt -w -8 -o $base.native $base.ml
rm $base.ml