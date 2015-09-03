#!/bin/sh -ex

cd ~/src/linearscan

(cd Hask; load-env-coq85 make)

# Avoid timestamps updates for files whose contents are unchanged
if [[ -d LinearScan ]]; then
    rsync -a --delete LinearScan/ LinearScan.base/
    load-env-coq85 make
    mv LinearScan LinearScan.new
    mv LinearScan.base LinearScan
    rsync -cr --delete LinearScan.new/ LinearScan/
    rm -fr LinearScan.new
else
    load-env-coq85 make
fi

xargs -0 <<EOF nix-cabal-shell --pure --command
       ghc --make Setup                         \
    && ./Setup configure --enable-tests         \
    && ./Setup build -j test                    \
    && ./dist/build/test/test $@
EOF
