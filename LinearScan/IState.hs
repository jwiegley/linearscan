module LinearScan.IState where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils


type IState errType i o a = i -> Prelude.Either errType ((,) a o)

ierr :: a1 -> IState a1 a2 a3 a4
ierr err x =
  Prelude.Left err

iget :: IState a1 a2 a2 a2
iget i =
  Prelude.Right ((,) i i)

iput :: a3 -> IState a1 a2 a3 ()
iput x x0 =
  Prelude.Right ((,) () x)

imap :: (a4 -> a5) -> (IState a1 a2 a3 a4) -> IState a1 a2 a3 a5
imap f x st =
  case x st of {
   Prelude.Left err -> Prelude.Left err;
   Prelude.Right p ->
    case p of {
     (,) a st' -> Prelude.Right ((,) (f a) st')}}

ipure :: a3 -> IState a1 a2 a2 a3
ipure x st =
  Prelude.Right ((,) x st)

ijoin :: (IState a1 a2 a3 (IState a1 a3 a4 a5)) -> IState a1 a2 a4 a5
ijoin x st =
  case x st of {
   Prelude.Left err -> Prelude.Left err;
   Prelude.Right p ->
    case p of {
     (,) y st' -> y st'}}

