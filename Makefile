COQFLAGS = ""
MISSING  = \
	find . -name '*.v' ! -name Notes.v ! -name CpdtTactics.v	\
                ! -name '*2.v'                             |		\
		xargs egrep -i -Hn '(admit|undefined)'     |		\
		      egrep -v 'Definition undefined'      |		\
		      egrep -v new/

all: Makefile.coq
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)
	$(MAKE) LinearScan/Main.hs
	@$(MISSING)

LinearScan/Main.hs: Main.vo
	@ls -1 *.hs | egrep -v '(Setup|LinearScan).hs' | \
	    while read file; do mv $$file LinearScan; done
	@perl -i -pe 's/import qualified (.*)/import qualified LinearScan.\1 as \1/' \
		LinearScan/*.hs
	@perl -i -pe 's/import qualified LinearScan\.Prelude as Prelude/import qualified Prelude\nimport qualified Data.List\nimport qualified Data.Ord\nimport qualified Data.Functor.Identity\nimport qualified LinearScan.Utils/' \
		LinearScan/*.hs
	@perl -i -pe 's/import qualified LinearScan\.GHC/import qualified GHC/'	\
		LinearScan/*.hs
	@perl -i -pe 's/unsafeCoerce :: a -> b/--unsafeCoerce :: a -> b/' \
		LinearScan/*.hs
	@perl -i -pe 's/module (.+?) where/module LinearScan.\1 where/' \
		LinearScan/*.hs
	@perl -i -pe 's/module LinearScan..+?.Utils where/module LinearScan.Utils where/' \
		LinearScan/Utils.hs
	@perl -i -pe 's/o -> Prelude.Either a \(\(,\) errType i\)/i -> Prelude.Either errType ((,) a o)/' LinearScan/IState.hs
	@perl -i -pe 's/a -> \(,\) i o/i -> (,) a o/' LinearScan/IState.hs
	@perl -i -pe 's/b -> \[\] \(LinearScan__Block g\)/g -> [] (LinearScan__Block b)/' \
		LinearScan/Main.hs
	@perl -i -pe 's/data Coq_simpl_fun/newtype Coq_simpl_fun/' LinearScan/*.hs

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@
	sed -i -e 's#./-dont-load-proofs#./.#g' $@
	sed -i -e 's#cd ./. ; .(MAKE) all#cd ./. ; echo $$(MAKE) all#' $@
	sed -i -e 's#cd \./\. ; .(MAKE) clean#cd ./. ; echo $$(MAKE) clean#' $@
	sed -i -e 's#cd \./\. && .(MAKE) clean#cd ./. ; echo $$(MAKE) clean#' $@
	sed -i -e 's#cd "./." && .(MAKE) all#cd ./. ; echo $$(MAKE) all#' $@

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	ls -1 LinearScan/* | egrep -v '(Utils).hs' | \
	    while read file; do rm -f $$file; done
	rm -f Makefile.coq Setup
	rm -fr dist .coq-native
