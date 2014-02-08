EXAMPLES=( list         \
           skiplist     \
           skiplist-kde \
           skiplist1    \
           skiplist2    \
           skiplist3    \
           skiplist4    \
           ticketint    \
           ticketset    \
         )

ALL_EXAMPLES=all_examples
DEPLOYMENT_FOLDER=deployment


./delete_vcs.sh;
rmdir $DEPLOYMENT_FOLDER;
mkdir $DEPLOYMENT_FOLDER;
rmdir $ALL_EXAMPLES;
mkdir $ALL_EXAMPLES;
for i in ${!EXAMPLES[*]} ; do
  ex=${EXAMPLES[$i]};
  zip -r9 $DEPLOYMENT_FOLDER/$ex.zip $ex;
  mkdir $ALL_EXAMPLES/$ex;
  cp -R $ex $ALL_EXAMPLES/$ex;
  echo $ale ;
done;
zip -r9 $DEPLOYMENT_FOLDER/$ALL_EXAMPLES.zip $ALL_EXAMPLES;
rm -rf $ALL_EXAMPLES
