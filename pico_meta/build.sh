#!/bin/sh
mkdir ../pico
PICOSRCDIR=../pico

maxsize=14

rm -f $PICOSRCDIR/pind*.v
cp pind_internal.v $PICOSRCDIR/pind_internal.v

echo "" > $PICOSRCDIR/pindall.v
for i in `seq 0 $maxsize`; do
  ./build-add.sh $i
done

echo -n "" > $PICOSRCDIR/pind.v
echo "From Fairness Require Export pindall." >> $PICOSRCDIR/pind.v
echo "From Paco Require Export pacotac." >> $PICOSRCDIR/pind.v
