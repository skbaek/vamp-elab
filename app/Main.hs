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

proofNames :: Proof -> Set Text
proofNames (Id_ _ nt nf) = S.fromList [nt, nf]
proofNames (Cut_ _ pf pt) = S.union (proofNames pf) (proofNames pt)
proofNames (FunC_ _ nts nf) = S.fromList (nf : nts)
proofNames (RelC_ _ nts nt nf) = S.fromList (nt : nf : nts)
proofNames (EqR_ _ nf) = S.fromList [nf]
proofNames (EqS_ _ nt nf) = S.fromList [nt, nf]
proofNames (EqT_ _ nxy nyz nxz) = S.fromList [nxy, nyz, nxz]
proofNames (NotT_ _ nm p) = S.insert nm $ proofNames p
proofNames (NotF_ _ nm p) = S.insert nm $ proofNames p
proofNames (OrT_ _ nm ps) = S.insert nm $ S.unions $ L.map proofNames ps
proofNames (OrF_ _ nm _ p) = S.insert nm $ proofNames p
proofNames (AndT_ _ nm _ p) = S.insert nm $ proofNames p
proofNames (AndF_ _ nm ps) = S.insert nm $ S.unions $ L.map proofNames ps
proofNames (ImpT_ _ nm pa pc) = S.insert nm $ S.union (proofNames pa) (proofNames pc)
proofNames (ImpFA_ _ nm p) = S.insert nm $ proofNames p
proofNames (ImpFC_ _ nm p) = S.insert nm $ proofNames p
proofNames (IffTO_ _ nm p) = S.insert nm $ proofNames p
proofNames (IffTR_ _ nm p) = S.insert nm $ proofNames p
proofNames (IffF_ _ nm po pr) = S.insert nm $ S.union (proofNames po) (proofNames pr)
proofNames (FaT_ _ nm _ p) = S.insert nm $ proofNames p
proofNames (FaF_ _ nm _ p) = S.insert nm $ proofNames p
proofNames (ExT_ _ nm _ p) = S.insert nm $ proofNames p
proofNames (ExF_ _ nm _ p) = S.insert nm $ proofNames p
proofNames (RelD_ _ p) = proofNames p
proofNames (AoC_ _ _ p) = proofNames p
proofNames (Open_ _) = S.empty

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

writeProof :: String -> Proof -> IO ()
writeProof nm prf = do
  Prelude.putStrLn $ "Writing proof : " <> nm
  TIO.writeFile nm $ tlt $ serList serText (S.toList $ proofNames prf) <> serProof prf

elaborate :: Bool -> String -> String -> String -> IO ()
elaborate vb tptp tstp cstp = do
  when vb $ pt "Reading problem and solution...\n"
  (ntf, sf, ftn, stps) <- hypsSteps vb tptp tstp
  when vb $ pt "Elaborating solution...\n"
  prf <- elab vb ntf sf ftn stps
  when vb $ pt "Writing proof : \n"
  writeProof cstp prf

mainArgs :: [String] -> IO ()
mainArgs (tptp : tstp : cstp : flags) = do
  (Just ()) <- timeout 60000000 (elaborate ("silent" `notElem` flags) tptp tstp cstp) 
  skip
mainArgs _ = error "invalid elab args"

main :: IO ()
main = getArgs >>= mainArgs