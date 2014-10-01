module Data.Vector0 where

import qualified Prelude
import qualified Data.List
import qualified Data.Fin as Fin


__ :: any
__ = Prelude.error "Logical or arity value used"

data Coq_t a =
   Coq_nil
 | Coq_cons a Prelude.Int (Coq_t a)

caseS :: (a1 -> Prelude.Int -> (Coq_t a1) -> a2) -> Prelude.Int -> (Coq_t 
         a1) -> a2
caseS h n v =
  case v of {
   Coq_nil -> __;
   Coq_cons h0 n0 t -> h h0 n0 t}

const :: a1 -> Prelude.Int -> Coq_t a1
const a n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    Coq_nil)
    (\n0 -> Coq_cons a n0
    (const a n0))
    n

replace :: Prelude.Int -> (Coq_t a1) -> Fin.Coq_t -> a1 -> Coq_t a1
replace n v p a =
  case p of {
   Fin.F1 k -> caseS (\h n0 t -> Coq_cons a n0 t) k v;
   Fin.FS k p' ->
    caseS (\h n0 t p2 -> Coq_cons h n0 (replace n0 t p2 a)) k v p'}

