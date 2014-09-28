This is an implementation of the optimized linear scan register allocator,
documented in the paper "Optimized Interval Splitting in a Linear Scan
Register Allocator" by Christian Wimmer and Hanspeter Mӧssenbӧck (a copy is
included in the `doc` subdirectory).

Although provided as a Haskell library, this library is implemented in the Coq
language and then extracted to Haskell.  It is being written both as research
into the capabilities of Coq to implement Haskell libraries, and for
experience in designing algorithms in Coq where correctness is paramount.
