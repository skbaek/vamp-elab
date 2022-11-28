{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

module Main where

import Basic
import Types
import PP
import Elab (elab)
import Parse

import Data.Text.Lazy as T (Text)
import Data.Text.Lazy.IO as TIO ( readFile, hPutStrLn, hPutStr, writeFile )
import System.Environment ( getArgs )
import System.Timeout (timeout)
import Control.Monad as M ( guard, MonadPlus(mzero), foldM_, when )
import Data.List as L 
import Data.Set as S
import Data.Map as HM

stepHypNames :: Step -> Set Text
stepHypNames (_, _, nms, _) = S.fromList nms

stepHyps :: Step -> [Text]
stepHyps (_, _, ns, _) = ns

addToHyps :: Set Text -> (NTF, Set Form, SFTN) -> PreAF -> (NTF, Set Form, SFTN)
addToHyps ahns hyp@(ntf, sf, ftn) (CnfAF n r tx)
  | S.member n ahns =
      let f = (conjecturize r $ univClose $ parseForm tx) in
      (HM.insert n f ntf, S.insert f sf, HM.insert (True, f) n ftn)
  | otherwise = hyp
addToHyps ahns hyp@(ntf, sf, ftn) (FofAF n r tx)
  | S.member n ahns =
      let f = (conjecturize r $ parseForm tx) in
      (HM.insert n f ntf, S.insert f sf, HM.insert (True, f) n ftn)
  | otherwise = hyp

hypsSteps :: Bool -> String -> String -> IO (NTF, Set Form, SFTN, [Step])
hypsSteps verbose tptp tstp = do
  pafs <- parsePreName tptp
  pb $ "Total hyps count =  " <> ppInt (L.length pafs) <> "\n"
  -- stps <- parseName tstp >>= mapM afToStep . sortAfs
  stps <- tstpToSteps tstp -- >>= mapM afToStep . sortAfs
  let ahns = L.foldl (\ ns_ -> L.foldl (flip S.insert) ns_ . stepHyps) S.empty stps
  let (ntf, sf, ftn) = L.foldl (addToHyps ahns) (HM.empty, S.empty, HM.empty) pafs
  pb $ "Active hyps count = " <> ppInt (HM.size ntf) <> "\n"
  Prelude.putStr $ tptp ++ "\n"
  when verbose $ mapM_ (\ (nm_, f_) -> pb (ft nm_ <> " :: " <> ppForm f_ <> "\n")) (HM.toList ntf)
  Prelude.putStr $ tstp ++ "\n"
  when verbose $ mapM_ (pb . ppStep) stps
  return (ntf, sf, ftn, stps)

writeProof :: String -> [Text] -> Proof -> IO ()
writeProof nm nms prf = do
  Prelude.putStrLn $ "Writing proof : " <> nm
  TIO.writeFile nm $ tlt $ serList serText nms <> serProof prf

elaborate :: Bool -> String -> String -> String -> IO ()
elaborate vb tptp tstp cstp = do
  when vb $ pt "Reading problem and solution...\n"
  (ntf, sf, ftn, stps) <- hypsSteps vb tptp tstp
  when vb $ pt "Elaborating solution...\n"
  let nms = L.foldl S.union S.empty (L.map stepHypNames stps)
  prf <- elab vb ntf sf ftn stps
  when vb $ pt "Writing proof : \n"
  writeProof cstp (S.toList nms) prf

mainArgs :: [String] -> IO ()
mainArgs (tptp : tstp : cstp : flags) = do
  (Just ()) <- timeout 60000000 (elaborate ("silent" `notElem` flags) tptp tstp cstp) 
  skip
mainArgs _ = error "invalid elab args"

main :: IO ()
main = getArgs >>= mainArgs