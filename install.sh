#!/bin/bash

dune build @install
echo 'build success'
echo '-------------------------------'
dune install
echo 'install success'
echo '-------------------------------'
why3 config --install-plugin $OPAM_SWITCH_PREFIX/lib/whylson/plugins/plugin_whylson.cmxs
echo '-------------------------------'
echo 'whylson installed successfully'
