MISSING  =								\
	find . -name '*.v' ! -name Notes.v				\
		! -name Extract.v					\
		! -name CpdtTactics.v					\
                ! -name '*2.v'                                    |	\
		xargs egrep -i -Hn '(Fail|abort|admit|undefined)' |	\
		      egrep -v 'Definition undefined'             |	\
		      egrep -v '(old|new|research)/'

all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all
	@$(MAKE) LinearScan/Main.hs
	-@$(MISSING) || exit 0

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
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq
	perl -i fixmake.pl $@

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq clean

fullclean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean fullclean force
