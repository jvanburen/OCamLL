#!/bin/sh -x

CONFIGURED_FLAG_FILE="./CONFIGURED_OPTICOMP"

if [ $(head -n 1 ./VERSION) != "4.04.0" ]; then
  echo "Version check failed, probably wrong directory?"
  exit 1
fi

if [ -f $CONFIGURED_FLAG_FILE ]; then
  echo 'Already configured'
else
  ./configure -flambda -prefix `pwd`/install
  echo 'Remove this file to re-configure' > $CONFIGURED_FLAG_FILE
fi

# using -j n makes this FAIL (not our fault)
make world
make opt

if [ $1 = "install" ]; then
  mkdir -p "install"
  make install
  echo "Installed to ./install/bin/ocamlopt"
fi
