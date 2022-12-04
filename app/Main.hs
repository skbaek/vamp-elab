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

stepHyps :: Step -> [BS]
stepHyps (_, _, ns, _) = ns

-- addToHyps :: Set BS -> (NTF, Set Form, SFTN) -> PreAF -> (NTF, Set Form, SFTN)
-- addToHyps ahns hyp@(ntf, sf, ftn) (CnfAF n r tx)
--   | S.member n ahns =
--       let f = (conjecturize r $ univClose $ parseForm tx) in
--       (HM.insert n f ntf, S.insert f sf, HM.insert (True, f) n ftn)
--   | otherwise = hyp
-- addToHyps ahns hyp@(ntf, sf, ftn) (FofAF n r tx)
--   | S.member n ahns =
--       let f = (conjecturize r $ parseForm tx) in
--       (HM.insert n f ntf, S.insert f sf, HM.insert (True, f) n ftn)
--   | otherwise = hyp

-- hypsSteps :: Bool -> String -> String -> IO (NTF, Set Form, SFTN, [Step])
-- hypsSteps vb tptp tstp = do
--   _
--   pafs <- parsePreName tptp
--   ps $ show $ "Total hyps count =  " <> ppInt (L.length pafs) <> "\n"
--   stps <- tstpToSteps tstp 
--   let ahns = L.foldl (\ ns_ -> L.foldl (flip S.insert) ns_ . stepHyps) S.empty stps
--   let (ntf, sf, ftn) = L.foldl (addToHyps ahns) (HM.empty, S.empty, HM.empty) pafs
--   ps $ show $ "Active hyps count = " <> ppInt (HM.size ntf) <> "\n"
--   Prelude.putStr $ tptp ++ "\n"
--   when verbose $ mapM_ (\ (nm_, f_) -> ps $ show (ft nm_ <> " :: " <> ppForm f_ <> "\n")) (HM.toList ntf)
--   Prelude.putStr $ tstp ++ "\n"
--   when verbose $ mapM_ (ps . show . ppStep) stps
--   return (ntf, sf, ftn, stps)

stepHypNames :: Step -> Set BS
stepHypNames (_, _, nms, _) = S.fromList nms

step :: Parser Step
step = anf >>= (cast . anfToStep)

tstp :: Parser [Step]
tstp = permStarL step

readSteps :: String -> IO [Step]
readSteps nm = BS.readFile nm >>= runParser (ign >> tstp) 

elaborate :: Bool -> String -> String -> String -> IO ()
elaborate vb pnm snm anm = do
  stps <- sortSteps <$> readSteps snm
  tptp <- readTptp pnm HM.empty
  let ivch = HM.foldrWithKey (\ nm_ f_ -> HM.insert (True, f_) nm_) HM.empty tptp
  prf <- elab vb tptp ivch stps
  writeProof anm prf

  -- when vb $ ps "Writing proof : \n"
  -- writeProof cstp (S.toList nms) prf
  


  -- when vb $ ps "Reading problem and solution...\n"
  -- (ntf, sf, ftn, stps) <- hypsSteps vb tptp tstp
  -- when vb $ ps "Elaborating solution...\n"
  -- let nms = L.foldl S.union S.empty (L.map stepHypNames stps)
  -- prf <- elab vb ntf sf ftn stps
  -- when vb $ ps "Writing proof : \n"

main :: IO ()
main = do 
  (tptp : tstp : cstp : flags) <- getArgs 
  let vb = "silent" `notElem` flags
  (Just ()) <- timeout 60000000 (elaborate vb tptp tstp cstp) 
  skip