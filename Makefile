COQFLAGS = ""
MISSING  = \
	find . -name '*.v' ! -name Notes.v ! -name CpdtTactics.v	\
                ! -name '*2.v'                             |		\
		xargs egrep -i -Hn '(admit|undefined)'     |		\
		      egrep -v 'Definition undefined'      |		\
		      egrep -v new/

all: Makefile.coq
	@$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)
	@$(MAKE) LinearScan/Main.hs
	@$(MISSING)

LinearScan/Main.hs: Main.vo
	@ls -1 *.hs | egrep -v '(Setup|LinearScan).hs' | \
	    while read file; do mv $$file LinearScan; done
	@perl -i fixcode.pl LinearScan/*.hs

Makefile.coq: _CoqProject
	@coq_makefile -f _CoqProject -o $@
	@perl -i fixmake.pl $@

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	ls -1 LinearScan/* | egrep -v '(Utils).hs' | \
	    while read file; do rm -f $$file; done
	rm -f Makefile.coq Setup
	rm -fr dist .coq-native
