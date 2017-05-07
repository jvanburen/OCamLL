#!/bin/bash -e

THIS_VERSION='Version: 3' # version of this config script
CONFIG_FILE="./CONFIGURED_OPTICOMP"
WORLD_FLAG="Remove this line to recompile world"

if [ $(head -n 1 ./VERSION) != "4.04.0" ]; then
  echo "[$0]: Version check failed, probably wrong directory?"
  exit 1
fi

COMPILED_WORLD=no

if [[ -r $CONFIG_FILE && $(head -n 1 $CONFIG_FILE) = $THIS_VERSION ]]
then
  CONFIGURED=yes
  echo "$0: Already configured" 1>&2
  if [[ $(tail -n 1 $CONFIG_FILE) = "$WORLD_FLAG" ]]
  then
    COMPILED_WORLD=yes
    echo "$0: Already compiled world" 1>&2
  else
    echo "$0: World needs recompiling" 1>&2
  fi
else
  CONFIGURED=no
  rm -f $CONFIG_FILE
  echo "$0: Not configured" 1>&2
fi

if [[ $CONFIGURED = yes ]]
then
  echo "$0: Remove $CONFIG_FILE to reconfigure" 1>&2
  rm -f middle_end/array_optimization.cm*
  rm -f middle_end/array_analysis.cm*
  rm -f middle_end/array_lattice.cm*
  rm -f middle_end/middle_end.cm*
else
  echo "$0: Reconfiguring build environment" 1>&2
  ./configure -flambda -prefix `pwd`/install 2>/dev/null
  echo $THIS_VERSION > $CONFIG_FILE
  echo 'Remove this file to re-configure' >> $CONFIG_FILE
  echo "$0: Reconfiguring done" 1>&2
fi

if [ $COMPILED_WORLD = no ]
then
  echo "$0: Recompiling world..." 1>&2
  make world --quiet
  echo $WORLD_FLAG >> $CONFIG_FILE
fi

# using -j n makes this FAIL (not our fault)
make opt --quiet

if [[ $CONFIGURED = no || $COMPILED_WORLD = no || ${1:-noinstall} = "install" ]]
then
  mkdir -p "install"
  make install --quiet
  echo "$0: Installed to ./install/bin/ocamlopt" 1>&2
else
  echo "$0: Skipping install" 1>&2
fi
