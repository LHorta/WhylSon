#!/bin/bash

dune build @install

dune install

why3 ide -L lib tests/lib_tests/Michelson/factorial.tz