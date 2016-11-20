#!/bin/sh
# Start coqide with the right -I options
# Use the Makefile to rebuild dependencies if needed
# Recompile the modified file after coqide editing

PWD=`pwd`
ARCH=$PWD/`sed -n -e 's/^ARCH=//p' Makefile.config`
VARIANT=$ARCH/`sed -n -e 's/^VARIANT=//p' Makefile.config`

make depend

make -q ${1}o || {
    make -j2 `grep "^${1}o" .depend | sed -e 's/.*://'`
}

COQPROGNAME="coqtop"
COQPROGARGS="\"-I\" \"~/gitrepos/PilkiLib\" \"-I\" \"~gitrepos/cases/src\" \"-R\" \"~/gitrepos/cases/theories\" \"Case_Tactics\" \"-I\" \"$PWD

		    /from_compcert\" \"-I\" \"$PWD/src\""


emacs --eval "(setq coq-prog-name \"$COQPROGNAME\")" \
 --eval "(setq coq-prog-args '($COQPROGARGS))" $1 \
&& make ${1}o
