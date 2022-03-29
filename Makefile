COQFLAGS = ""
MISSING  =								\
	find . -name '*.v' ! -name Notes.v				\
		! -name Extract.v					\
		! -name CpdtTactics.v					\
                ! -name '*2.v'                                    |	\
		xargs egrep -i -Hn '(Fail|abort|admit|undefined)' |	\
		      egrep -v 'Definition undefined'             |	\
		      egrep -v '(old|new|research)/'

VFILES = $(wildcard src/*.v)
VOFILES = $(patsubst %.v,%.vo,$(VFILES))

all: $(VOFILES) LinearScan/Main.hs
	-@$(MISSING) || exit 0

%.vo: %.v Makefile.coq
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)
	@$(MAKE) LinearScan/Main.hs

LinearScan/Main.hs: src/Main.vo
	@if [ ! -d LinearScan ]; then rm -f LinearScan; fi
	@if [ ! -d LinearScan ]; then mkdir LinearScan; fi
	@ls -1 *.hs | egrep -v '(Setup|LinearScan).hs' |	\
	    while read file; do					\
              if ! grep "module LinearScan" $$file; then	\
	        perl -i fixcode.pl $$file;			\
              fi;						\
	      if [ "$$file" = "eqtype.hs" ]; then		\
                mv eqtype.hs LinearScan/Eqtype.hs;		\
	      elif [ "$$file" = "choice.hs" ]; then		\
                mv choice.hs LinearScan/Choice.hs;		\
	      elif [ "$$file" = "fintype.hs" ]; then		\
                mv fintype.hs LinearScan/Fintype.hs;		\
	      elif [ "$$file" = "seq.hs" ]; then		\
                mv seq.hs LinearScan/Seq.hs;			\
	      elif [ "$$file" = "ssrbool.hs" ]; then		\
                mv ssrbool.hs LinearScan/Ssrbool.hs;		\
	      elif [ "$$file" = "ssreflect.hs" ]; then		\
                mv ssreflect.hs LinearScan/Ssreflect.hs;	\
	      elif [ "$$file" = "ssrfun.hs" ]; then		\
                mv ssrfun.hs LinearScan/Ssrfun.hs;		\
	      elif [ "$$file" = "ssrnat.hs" ]; then		\
                mv ssrnat.hs LinearScan/Ssrnat.hs;		\
              else						\
                mv $$file LinearScan;				\
	      fi						\
            done

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@
	perl -i fixmake.pl $@

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Setup LinearScan/*
	rm -fr dist .coq-native
	rm -fr .hdevtools.sock *.glob *.d *.vo
