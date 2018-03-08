module Sessioned where

import Common
import Control.Monad
import Data.Parameterized.Some
import qualified Data.Map.Strict as Map

import qualified Core as C
import qualified Numeric.Probability.Distribution as P

-- first 
type Party p mi mo = SomeExp -> Exp (mi + ()) -> P.T p (SomeExp, Exp (mo + ()))

data Sched p mi mo where
  SNil :: Sched p () ()
  SCons :: Sched p mi mo' -> Party p mo' mo -> PID -> Sched p mi mo

type Trace a = (Exp (a + ()), [SomeExp], Map.Map PID (SomeExp))

runSched_ :: Num p => Sched p a t -> Trace a  -> P.T p (Trace t)
runSched_ (SCons sch p pid) tr = do
  (ei, es, sm) <- runSched_ sch tr
  case (Map.lookup pid sm) of
    Just s -> do
      (s', eo) <- p s ei
      return $ (eo, (SomeExp ei) : es, Map.insert pid s' sm)
    Nothing -> do
      (s', eo) <- p (SomeExp EUnit) ei
      return $ (eo, (SomeExp ei) : es, Map.insert pid s' sm)
runSched_ (SNil) tr = return tr

runSched :: Num p => Sched p () t -> Map.Map PID SomeExp -> P.T p (Trace t)
runSched sch smap = runSched_ sch (EInl EUnit, [], smap)



compileParty :: Party p mi mo -> C.Party p
compileParty p = \inbuf -> do
  error "unimp"
  
  
