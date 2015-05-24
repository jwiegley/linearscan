COQFLAGS = ""
MISSING  = \
	find . -name '*.v' ! -name Notes.v ! -name CpdtTactics.v	\
                ! -name '*2.v'                                   |	\
		xargs egrep -i -Hn '(abort|admit|undefined)'     |	\
		      egrep -v 'Definition undefined'            |	\
		      egrep -v '(old|new|research)/'

VFILES = $(wildcard src/*.v)
VOFILES = $(patsubst %.v,%.vo,$(VFILES))

all: $(VOFILES) LinearScan/Main.hs		\
     LinearScan/Eqtype.hs			\
     LinearScan/Choice.hs			\
     LinearScan/Fintype.hs			\
     LinearScan/Seq.hs				\
     LinearScan/Ssrbool.hs			\
     LinearScan/Ssreflect.hs			\
     LinearScan/Ssrfun.hs			\
     LinearScan/Ssrnat.hs
	-@$(MISSING) || exit 0

%.vo: %.v Makefile.coq
	@$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)
	@$(MAKE) LinearScan/Main.hs

LinearScan/Main.hs: src/Main.vo
	@ls -1 *.hs | egrep -v '(Setup|LinearScan).hs' | \
	    while read file; do mv $$file LinearScan; done
	@perl -i fixcode.pl LinearScan/*.hs

LinearScan/Eqtype.hs: LinearScan/eqtype.hs
	@mv $< $@

LinearScan/Choice.hs: LinearScan/choice.hs
	@mv $< $@

LinearScan/Fintype.hs: LinearScan/fintype.hs
	@mv $< $@

LinearScan/Seq.hs: LinearScan/seq.hs
	@mv $< $@

LinearScan/Ssrbool.hs: LinearScan/ssrbool.hs
	@mv $< $@

LinearScan/Ssreflect.hs: LinearScan/ssreflect.hs
	@mv $< $@

LinearScan/Ssrfun.hs: LinearScan/ssrfun.hs
	@mv $< $@

LinearScan/Ssrnat.hs: LinearScan/ssrnat.hs
	@mv $< $@

Makefile.coq: _CoqProject
	@coq_makefile -f _CoqProject -o $@
	@perl -i fixmake.pl $@

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	ls -1 LinearScan/* | egrep -v '(Utils).hs' | \
	    while read file; do rm -f $$file; done
	rm -f Makefile.coq Setup
	rm -fr dist .coq-native
	rm -fr .hdevtools.sock *.glob *.d *.vo
