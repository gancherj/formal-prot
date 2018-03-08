module Sessioned where

import Common
import Control.Monad
import Data.Parameterized.Some
import qualified Data.Map.Strict as Map

import qualified Core as C
import qualified Numeric.Probability.Distribution as P

-- inr means error
type Party p mi mo = Exp Any -> Exp (mi + ()) -> P.T p (Exp Any, Exp (mo + ()))

data Sched p mi mo where
  SNil :: Sched p () ()
  SCons :: Sched p mi mo' -> Party p mo' mo -> PID -> Sched p mi mo

type Trace a = (Exp (a + ()), [Exp Any], Map.Map PID (Exp Any))

runSched_ :: Num p => Sched p a t -> Trace a  -> P.T p (Trace t)
runSched_ (SCons sch p pid) tr = do
  (ei, es, sm) <- runSched_ sch tr
  case (Map.lookup pid sm) of
    Just s -> do
      (s', eo) <- p s ei
      return $ (eo, (EDyn ei) : es, Map.insert pid s' sm)
    Nothing -> do
      (s', eo) <- p (EDyn EUnit) ei
      return $ (eo, (EDyn ei) : es, Map.insert pid s' sm)
runSched_ (SNil) tr = return tr

runSched :: Num p => Sched p () t -> Map.Map PID (Exp Any) -> P.T p (Trace t)
runSched sch smap = runSched_ sch (EInl EUnit, [], smap)

-- Conversion of parties from sessioned system to unsessioned. This conversion requires information about both the party's own identity and the identities of the parties it is communicating with.
-- With the PIDs self, msgfrom, and msgto, an unsessioned party will look for a message from itself. This is used as its state. It then looks in its input buffer for a message from msgfrom. If it finds one, this is fed into the sessioned party. If one is not found, error is fed to the party. The sessioned party will then output a new state and a new message. The corresponding sends then happen.
compileParty :: PID -> PID -> PID -> Party p mi mo -> C.Party p
compileParty self msgfrom msgto p = \inbuf -> do
  error "unimp"
  
  
