#!/bin/bash

build_check=0
install_check=0

dune build @install
if [ $? -eq 0 ]; then
    echo '-------------------------------'
    echo 'build success'
    echo '-------------------------------'
    let build_check=1
    dune install
fi

# check installation 
if [ $? -eq 0  -a $build_check -eq 1 ]; then
    echo '-------------------------------'
    echo 'install success'
    echo '-------------------------------'
    let install_check=1
fi

if [ $build_check -eq 1 -a $install_check -eq 1 ]; then
    why3 config --install-plugin $OPAM_SWITCH_PREFIX/lib/whylson/plugins/plugin_whylson.cmxs
    echo '-------------------------------'
    echo 'WhylSon installed successfully!'
    echo '-------------------------------'
fi


