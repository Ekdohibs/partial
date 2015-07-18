#!/bin/sh
ocamlc -c parser.mli
ocamlopt -w -8 -c parser.ml
ocamlopt -w -8 -c main.ml
ocamlopt -o compiler parser.cmx main.cmx