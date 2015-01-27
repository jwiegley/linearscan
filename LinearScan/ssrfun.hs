module LinearScan.Ssrfun where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils


_Option__apply :: (a1 -> a2) -> a2 -> (Prelude.Maybe a1) -> a2
_Option__apply f x u =
  case u of {
   Prelude.Just y -> f y;
   Prelude.Nothing -> x}

_Option__coq_default :: a1 -> (Prelude.Maybe a1) -> a1
_Option__coq_default =
  _Option__apply (\x -> x)

_Option__bind :: (a1 -> Prelude.Maybe a2) -> (Prelude.Maybe a1) ->
                 Prelude.Maybe a2
_Option__bind f =
  _Option__apply f Prelude.Nothing

_Option__map :: (a1 -> a2) -> (Prelude.Maybe a1) -> Prelude.Maybe a2
_Option__map f =
  _Option__bind (\x -> Prelude.Just (f x))

