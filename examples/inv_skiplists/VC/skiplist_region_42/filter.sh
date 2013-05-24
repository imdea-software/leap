#!/bin/sh
NAME=$1
FILE=$2
if [ ! -f "$FILE" ]; then 
    exit 0
fi

TIME=`grep "Total analysis" $FILE | awk '{ print $5}'`
OUTCOME=`grep "TSL DP verified" $FILE | awk '{ print $5}'`
if [ "$OUTCOME" == "1" ]; then
    VERIFIED="ok"
else
    VERIFIED="NO"
fi

echo ${NAME} : ${TIME} : ${VERIFIED}
