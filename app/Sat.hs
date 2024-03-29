{-# LANGUAGE OverloadedStrings #-}

module Sat where 

-- import System.Environment
import System.Process
import Types
import LocalTypes
import Basic
import PP
import Data.List as L
import Data.Map as HM (Map, lookup, insert, map, empty)
import Data.Set as S (Set, insert, fromList, empty)
import Data.Functor ((<&>))
import Control.Monad as M (guard, foldM, foldM_, (>=>), mzero)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Builder as BD
import Debug.Trace (trace)

formToLit :: Form -> Maybe Form
formToLit (Not (Not f)) = formToLit f
formToLit (Not (Rel r xs)) = return $ Not (Rel r xs)
formToLit (Rel r xs) = return $ Rel r xs
formToLit _ = Nothing

formToDisjs :: Form -> [Form]
formToDisjs (Or fs) = fs
formToDisjs f = [f]

formToLits :: Form -> Maybe [Form]
formToLits f = mapM formToLit $ formToDisjs f

litToAtom :: Form -> Maybe Form
litToAtom (Rel r xs) = return $ Rel r xs
litToAtom (Not (Rel r xs)) = return $ Rel r xs
litToAtom _ = Nothing

litToNum :: [Form] -> Form -> Maybe Int
litToNum as (Not a) = do
  k <- L.elemIndex a as
  return $ - (k + 1)
litToNum as a = do
  k <- L.elemIndex a as
  return $ k + 1

litsToNums :: [Form] -> [Form] -> Maybe [Int]
litsToNums as = mapM (litToNum as)

removeLastZero :: [BS] -> Maybe [BS]
removeLastZero [] = Nothing
removeLastZero ["0"] = Just []
removeLastZero (t : ts) = removeLastZero ts <&> (t :)

removeMidLastZero :: [BS] -> Maybe ([BS], [BS])
removeMidLastZero [] = Nothing
removeMidLastZero ("0" : ts) = do
  ts' <- removeLastZero ts
  return ([], ts')
removeMidLastZero (t : ts) = do
  (ts0, ts1) <- removeMidLastZero ts
  return (t : ts0, ts1)

intToLit :: [Form] -> Int -> Maybe Form
intToLit as k =
  if k < 0
  then nth (abs k - 1) as <&> Not
  else nth (k - 1) as

bssToLrat :: [Form] -> [BS] -> Maybe Lrat
bssToLrat _ (t : "d" : ts) = do
  k <- bs2int t
  ks <- removeLastZero ts >>= mapM bs2int
  return $ Del k ks
bssToLrat as (t : ts) = do
  k <- bs2int t
  (ts0, ts1) <- removeMidLastZero ts
  fs <- mapM (bs2int >=> intToLit as) ts0
  ks <- mapM bs2int ts1
  return $ Add k fs ks
bssToLrat _ _ = Nothing

useRgtLit :: Form -> Prf
useRgtLit (Not f) = NotF' f $ Id' f
useRgtLit f = NotF' f $ Id' f

useLftLit :: Form -> Prf
useLftLit (Not f) = NotT' f $ Id' f
useLftLit f = NotT' f $ Id' f

lratPrf :: Map Int Form -> [Form] -> [Int] -> IO Prf
lratPrf fs [] hs = lratPrfCore fs S.empty hs
lratPrf fs ls hs = do 
  let nls = L.map negLit ls  
  let nlps = L.map (\ l_ -> (negLit l_, useRgtLit l_)) ls 
  let fxs = S.fromList nls
  p <- lratPrfCore fs fxs hs
  return $ Cut' (And nls) (OrF' ls ls $ AndF' nlps) (AndT' nls nls p)

lratsPrf :: Map Int Form -> [Lrat] -> IO Prf
lratsPrf _ [] = error "Empty LRAT proof"
lratsPrf fs [Add _ [] hs] = do 
  p <- lratPrf fs [] hs 
  return $ Cut' Bot p BotT'
lratsPrf fs (Add k ls hs : lrs) = do 
  guardMsg "Empty clause detected" (not $ null ls)
  p0 <- lratPrf fs ls hs 
  let fs' = HM.insert k (Or ls) fs
  p1 <- lratsPrf fs' lrs 
  return $ Cut' (Or ls) p0 p1
lratsPrf fs (_ : lrs) = lratsPrf fs lrs

lratCtx :: Int -> [Form] -> Map Int Form
lratCtx _ [] = HM.empty
lratCtx k (f : fs) = HM.insert k f $ lratCtx (k + 1) fs

negLit :: Form -> Form
negLit (Not f) = f
negLit f = Not f

negated :: Set Form -> Form -> Bool
negated fs (Not f) = f `elem` fs
negated fs f = Not f `elem` fs

useLastCla :: Set Form -> Form -> IO Prf 
useLastCla fxs (Or fs)  
  | L.all (negated fxs) fs = return $ OrT' $ L.map (\ f_ -> (f_, useLftLit f_)) fs
useLastCla fxs f  
  | negated fxs f = return $ useLftLit f
useLastCla _ _ = error "use last claus"

lratPrfCore :: Map Int Form -> Set Form -> [Int] -> IO Prf
lratPrfCore _ _ [] = error "lrat : hints exhausted"
lratPrfCore fs fxs [h] = do 
  f <- cast $ HM.lookup h fs 
  useLastCla fxs f 
lratPrfCore fs fxs (h : hs) = do
  f <- cast $ HM.lookup h fs 
  l <- findNewLit fxs f
  let cl = negLit l
  let fxs0 = S.insert cl fxs
  let fxs1 = S.insert l fxs
  p0 <- useCla fxs0 f 
  p1 <- lratPrfCore fs fxs1 hs 
  return $ Cut' l (movLitLft l p0) p1

movLitLft :: Form -> Prf -> Prf
movLitLft (Not f) p = NotF' f p
movLitLft f p = Cut' (Not f) (NotF' f $ Id' f) p

useCla :: Set Form -> Form -> IO Prf
useCla fxs (Or fs) = do
  guardMsg "not all negated" $ L.all (negated fxs) fs
  return $ OrT' $ L.map (\ f_ -> (f_, useLftLit f_)) fs
useCla fxs f = do
  guardMsg "not all negated" $ negated fxs f
  return $ useLftLit f

findNewLit :: Set Form -> Form -> IO Form
findNewLit fxs (Or fs) = cast $ breakSingleton $ nub $ L.filter (not . negated fxs) fs
findNewLit fxs f 
  | isLit f && not (negated fxs f) = return f 
  | otherwise = error "cannot find new lit"

sat :: [Form] -> IO Prf
sat fs = do
  lss <- cast $ mapM formToLits fs
  as <- cast $ mapM litToAtom (L.concat lss) <&> nub
  nss <- cast $ mapM (litsToNums as) lss
  let max = L.length as
  let head = "p cnf " <> ppInt max <> " " <> ppInt (L.length nss)
  let body = L.map (\ ns -> ppInter " " $ L.map ppInt $ ns ++ [0]) nss
  let dimacs = ppInter "\n" $ head : body
  BD.writeFile "temp.cnf" dimacs
  ps "Running cadical...\n"
  runCommand "cadical -q temp.cnf temp.drat" >>= waitForProcess
  ps "Running drat-trim...\n"
  runCommand "drat-trim temp.cnf temp.drat -L temp.lrat" >>= waitForProcess
  ps "Reading LRAT proof file...\n"
  t <- BS.readFile "temp.lrat"
  runCommand "rm temp.*" >>= waitForProcess
  let lns = L.map (BS.split $ c2w ' ') $ L.filter (not . BS.null) $ BS.split (c2w '\n') t
  ps "Parsing LRAT proof...\n"
  lrs <- mapM (cast . bssToLrat as) lns
  ps "Assembing proof...\n"
  p <- lratsPrf (lratCtx 1 fs) lrs 
  ps "SAT step success!\n"
  return p