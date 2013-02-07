
cppo -D 'RAISE(e) (LOG "Exception raised" EXN (e) LEVEL ERROR; raise(e))' $1 -o $1;
camlp4o bolt_pp.cmo $1

