{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

module Main where

import Basic
import Types
import LocalTypes
import PP
import Elab (elab)
import Parse 
import System.Environment ( getArgs )
import System.Timeout (timeout)
import Control.Monad as M ( guard, MonadPlus(mzero), foldM_, when )
import Data.List as L 
import Data.Set as S
import Data.Map as HM
import qualified Data.ByteString as BS
import qualified Data.ByteString.Builder as BD

stepHyps :: Step -> [BS]
stepHyps (_, _, ns, _) = ns

stepHypNames :: Step -> Set BS
stepHypNames (_, _, nms, _) = S.fromList nms

step :: Parser Step
step = anf >>= (cast . anfToStep)

tstp :: Parser [Step]
tstp = permStarL step

readSteps :: String -> IO [Step]
readSteps nm = BS.readFile nm >>= runParser (ign >> tstp) 

elaborate :: Bool -> String -> String -> String -> IO ()
elaborate vb pnm snm enm = do
  stps <- sortSteps <$> readSteps snm
  tptp <- readTptp pnm HM.empty
  let ivch = HM.foldrWithKey (\ nm_ f_ -> HM.insert (True, f_) nm_) HM.empty tptp
  prf <- elab vb tptp ivch stps
  BD.writeFile enm $ ppListNl ppElab $ linearize prf

mapAnfOnce :: (Anf -> IO ()) -> BS -> IO BS 
mapAnfOnce fun bs = 
  case parse anf bs of
    Just (anf, bs') -> do 
      fun anf 
      return bs'
    _ -> snd <$> cast (parse inc bs)

mapAnfCore :: (Anf -> IO ()) -> BS -> IO () 
mapAnfCore fun bs
  | BS.null bs = skip
  | otherwise = do 
    bs' <- mapAnfOnce fun bs
    mapAnfCore fun bs'

mapAnf :: String -> (Anf -> IO ()) -> IO () 
mapAnf fnm fun = do
 txt <- BS.readFile fnm
 (_, txt') <- cast $ parse ign txt 
 mapAnfCore fun txt'

checkBadName :: Anf -> IO ()
checkBadName ('e' :> tl, _, _, _) = 
  case bs2int tl of 
    Just k -> error $ "e-number detected : " ++ bd2str (ppInt k) ++ "\n"
    _ -> skip
checkBadName (nm, _, _, _) = skip -- pbs $ "Good name : " <> nm <> "\n"
-- 
-- main :: IO ()
-- main = do 
--   [pnm] <- getArgs 
--   mapAnf pnm checkBadName
-- 
main :: IO ()
main = do 
  (tptp : tstp : cstp : flags) <- getArgs 
  let vb = "silent" `notElem` flags
  (Just ()) <- timeout 120000000 (elaborate vb tptp tstp cstp) 
  skip