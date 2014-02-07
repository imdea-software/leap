for i in `find src/* -type f | grep -v \\.swp | grep -v \\.svn` ; do
	sed -i "" 's/'$1'/'$2'/g' $i ; done

#	LinuxVersion sed -i 's/'$1'/'$2'/g' $i ; done
#	MacVersion sed -i "" 's/'$1'/'$2'/g' $i ; done
