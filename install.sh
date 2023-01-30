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
    echo 'WhylSon install successfully!'
    echo '-------------------------------'
    let install_check=1
fi


