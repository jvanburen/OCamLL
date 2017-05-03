#!/bin/sh -e

CONFIGURED_FLAG_FILE="./CONFIGURED_OPTICOMP"

if [ $(head -n 1 ./VERSION) != "4.04.0" ]; then
  echo "Version check failed, probably wrong directory?"
  exit 1
fi

if [ -f $CONFIGURED_FLAG_FILE ]; then
  echo 'Already configured'
else
  ./configure -flambda -prefix `pwd`/install
  make world
  echo 'Remove this file to re-configure' > $CONFIGURED_FLAG_FILE
fi

# using -j n makes this FAIL (not our fault)
make opt

if [ ${1:-noinstall} = "noinstall" ]; then
  echo "skipping installation"
else
  mkdir -p "install"
  make install
  echo "Installed to ./install/bin/ocamlopt"
fi
