#!/bin/sh

if [ $# -lt 1 ]
then
  echo "Usage: $0 relsize"
  exit 1
fi

PICOSRCDIR=../pico

relsize=$1

python pind.py ${relsize} > $PICOSRCDIR/pind${relsize}.v;
echo "From Fairness Require Export pind${relsize}." >> $PICOSRCDIR/pindall.v;
