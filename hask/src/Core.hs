module Core where

import Common
import Control.Monad
import Data.List
import Data.SBV
import qualified Data.Set as Set
import qualified Numeric.Probability.Distribution as P
import Data.Parameterized.Some


type Buf = [(PID, PID, Some Exp)]
type PBuf = [(PID, Some Exp)]

type Party p = PBuf -> P.T p PBuf

type Trace = (Int, Buf, Buf)

type Schedule p = [(Party p, PID, Bool)] -- bool = is corrupt

forP :: PID -> (PID, PID, Some Exp) -> Bool
forP pid (_, to, _) = to == pid

fromP :: PID -> (PID, PID, Some Exp) -> Bool
fromP pid (from, _, _) = from == pid
  
eraseFrom :: Buf -> PBuf
eraseFrom buf =
  map (\(a,b,c) -> (a,c)) buf

insertFrom :: PID -> PBuf -> Buf
insertFrom pid =
  map (\(to, m) -> (pid, to, m))


runParty :: Num p => Trace -> Party p -> PID -> P.T p Trace
runParty (i, bU, bP) p pid = do
  let (bUP, buNotP) = partition (forP pid) bU
  pouts <- p (eraseFrom bUP)
  return (i+1, buNotP ++ (insertFrom pid pouts), bP ++ bUP)


runSchedule :: Num p => Schedule p -> Trace -> P.T p Trace
runSchedule s t = foldM (\tr (p, pid, _) -> runParty tr p pid) t s

crupt :: Schedule p -> Set.Set PID
crupt s = Set.unions $ map (\(_, pid, c) -> if c then Set.singleton pid else Set.empty) s

proj :: Buf -> Set.Set PID -> Buf
proj b pids =
  filter (\(from, to, _) -> (from `Set.member` pids) || (to `Set.member` pids)) b



  
