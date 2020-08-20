#! /usr/bin/env bash

set -o errexit
set -o pipefail
set -o nounset
set -o xtrace

if [ ! -d .cabal ]; then
    mkdir .cabal
fi

if [ ! -L ~/.cabal ]; then
    DIR=$(pwd)
    pushd ~
    ln -s "$DIR/.cabal" .cabal
    popd
fi

cabal v2-build
cp $(find dist-newstyle -name zaphod -type f) .

cabal v2-run zaphod
