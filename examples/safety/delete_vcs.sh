for i in `ls -d */` ; do rm -f ${i%%/}/vcs/*.vcfile ; done
