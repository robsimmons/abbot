#!/bin/bash

root=$(git rev-parse --show-toplevel)

for dir in $(find $root/examples/ -mindepth 1 -maxdepth 1 -type d | rev | cut -d '/' -f 1 | rev); do
  echo $dir
  {
    echo "(library
 (name abbot_"$dir"_examples)
 (public_name abbot."$dir"_examples)
 (preprocess (pps ppx_jane))
 (libraries
  abbot_runtime
  core))"

    for abbot_file in $(ls -1 $root/examples/$dir | grep "\.abt$"); do
      basename=$(echo $abbot_file | sed "s/\.abt//")
      echo ""
      echo "(rule
 (targets
  "$basename"_intf.ml
  "$basename".mli
  "$basename".ml
  "$basename".sig
  "$basename".sml)
 (deps
  (:abbot ../../bin/main.exe)
  (:example "$basename".abt))
 (action
  (progn
   (run %{abbot} ocaml %{example})
   (run %{abbot} sml %{example}))))"
    done
  } > $root/examples/$dir/dune
done
