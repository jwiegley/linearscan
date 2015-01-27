module LinearScan.State where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils


type State s a = s -> (,) a s

get :: State a1 a1
get i =
  (,) i i

put :: a1 -> State a1 ()
put x x0 =
  (,) () x

modify :: (a1 -> a1) -> State a1 ()
modify f i =
  (,) () (f i)

join :: (State a1 (State a1 a2)) -> State a1 a2
join x st =
  case x st of {
   (,) y st' -> y st'}

fmap :: (a2 -> a3) -> (State a1 a2) -> State a1 a3
fmap f x st =
  case x st of {
   (,) a st' -> (,) (f a) st'}

bind :: (a2 -> State a1 a3) -> (State a1 a2) -> State a1 a3
bind f x =
  join (fmap f x)

pure :: a2 -> State a1 a2
pure x st =
  (,) x st

ap :: (State a1 (a2 -> a3)) -> (State a1 a2) -> State a1 a3
ap f x st =
  case f st of {
   (,) f' st' ->
    case x st' of {
     (,) x' st'' -> (,) (f' x') st''}}

liftA2 :: (a2 -> a3 -> a4) -> (State a1 a2) -> (State a1 a3) -> State a1 a4
liftA2 f x y =
  ap (fmap f x) y

mapM :: (a2 -> State a1 a3) -> ([] a2) -> State a1 ([] a3)
mapM f l =
  case l of {
   [] -> pure [];
   (:) x xs -> liftA2 (\x0 x1 -> (:) x0 x1) (f x) (mapM f xs)}

foldM :: (a2 -> a3 -> State a1 a2) -> a2 -> ([] a3) -> State a1 a2
foldM f s l =
  case l of {
   [] -> pure s;
   (:) y ys -> bind (\x -> foldM f x ys) (f s y)}

forFoldM :: a2 -> ([] a3) -> (a2 -> a3 -> State a1 a2) -> State a1 a2
forFoldM s l f =
  foldM f s l

concat :: ([] ([] a1)) -> [] a1
concat l =
  case l of {
   [] -> [];
   (:) x xs -> (Prelude.++) x (concat xs)}

concatMapM :: (a2 -> State a1 ([] a3)) -> ([] a2) -> State a1 ([] a3)
concatMapM f l =
  fmap concat (mapM f l)

