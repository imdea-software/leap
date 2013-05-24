TSL=../../../../tsl
OPTIONS=-z3 
ECHO=/opt/local/bin/gecho

BASENAME=42
EXT=1-1 1-2 1-3 1-4 1-5 1-6 1-7 1-8
ALL := $(addsuffix .vc, $(addprefix ${BASENAME}.,${EXT}))
OUT := $(addsuffix .out, $(addprefix ${BASENAME}.,${EXT}))
STAT:= $(addsuffix .stat, $(addprefix ${BASENAME}.,${EXT}))


table: ${STAT}
	cat ${STAT}

all: ${OUT}
	@echo ${OUT}

%.out: %.vc
	$(TSL) $(OPTIONS) $< > $@


%.stat: %.out
	@./filter.sh `basename $< .out` $< > $@
	@(cat $@)



clean: 
	rm -f ${OUT} ${STAT}
