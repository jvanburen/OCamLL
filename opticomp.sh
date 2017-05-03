#!/bin/sh -x

CONFIGURED_FLAG_FILE="./OPTICOMP_CONFIGURED"

if [ $(head -n 1 ./VERSION) != "4.04.0" ]; then
  echo "Version check failed, probably wrong directory?"
  exit 1
fi

mkdir -p "install"

if [ -f $CONFIGURED_FLAG_FILE ]; then
  echo 'Already configured'
else
  ./configure -flambda -prefix `pwd`/install
  echo 'Remove this file to re-configure' > $CONFIGURED_FLAG_FILE
fi

make world
make opt

make install

echo "Installed to ./install/bin/ocamlopt"
