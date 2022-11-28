{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Elab where

import Types
import Basic
import PP 
import Prove 
import Lem (impFAC, impToOrNot, rDefLemma1)
import Sat (sat)
-- import Expand (stelabsToElabs)
import Check (isRelD, verify)

import Data.List as L (all, map, foldl, length, reverse, findIndex, concatMap, mapAccumL, elemIndex)
import Data.Map as HM (insert, lookup, Map, empty, toList, member, notMember)
import Data.Set as S (Set, insert, singleton, toList, member)
import Data.Text.Lazy as T (Text, intercalate)
import Data.Text.Lazy.Builder (Builder)
import Control.Monad as M ( guard, MonadPlus(mzero), foldM, foldM_, when )
import Control.Monad.Fail as MF (MonadFail, fail)
import Control.Applicative ( Alternative((<|>)) )
import Data.Bifunctor as DBF (first, second, bimap)
import Norm (fltn)
import GHC.Stack (pushCallStack)

rfsj :: Form -> Form
rfsj (Not f) = Not $ rfsj f
rfsj (Imp f g) = Imp (rfsj f) (rfsj g)
rfsj (Iff f g) = Iff (rfsj f) (rfsj g)
rfsj (Or fs) =
  case L.map rfsj fs of
    [f] -> f
    fs' -> Or fs'
rfsj (And fs) =
  case L.map rfsj fs of
    [f] -> f
    fs' -> And fs'
rfsj (Fa vs f) = Fa vs $ rfsj f
rfsj (Ex vs f) = Ex vs $ rfsj f
rfsj f@(Rel _ _) = f
rfsj f@(Eq _ _) = f

rpsj :: Prf -> Prf
rpsj (Id' f) = Id' $ rfsj f
rpsj p@(EqR' _) = p
rpsj p@(EqS' _ _) = p
rpsj p@EqT' {} = p
rpsj p@FunC' {} = p
rpsj p@RelC' {} = p
rpsj (NotT' f p) = NotT' (rfsj f) (rpsj p)
rpsj (NotF' f p) = NotF' (rfsj f) (rpsj p)
rpsj (OrT' [(f, p)]) = rpsj p
rpsj (OrT' ps) = OrT' $ L.map (bimap rfsj rpsj) ps
rpsj (AndF' [(f, p)]) = rpsj p
rpsj (AndF' ps) = AndF' $ L.map (bimap rfsj rpsj) ps
rpsj (AndT' [f] gs p) =
  case gs of
    [g] -> if f == g then rpsj p else et "rpsj-and-lft-0"
    _ -> et "rpsj-and-lft-1"
rpsj (AndT' fs gs p) = AndT' (L.map rfsj fs) (L.map rfsj gs) (rpsj p)
rpsj (OrF' [f] gs p) =
  case gs of
    [g] -> if f == g then rpsj p else et "rpsj-or-rgt-0"
    _ -> et "rpsj-or-rgt-1"
rpsj (OrF' fs gs p) = OrF' (L.map rfsj fs) (L.map rfsj gs) (rpsj p)
rpsj (ImpFA' f g p) = ImpFA' (rfsj f) (rfsj g) (rpsj p)
rpsj (ImpFC' f g p) = ImpFC' (rfsj f) (rfsj g) (rpsj p)
rpsj (ImpT' f g pf pg) = ImpT' (rfsj f) (rfsj g) (rpsj pf) (rpsj pg)
rpsj (IffTO' f g p) = IffTO' (rfsj f) (rfsj g) (rpsj p)
rpsj (IffTR' f g p) = IffTR' (rfsj f) (rfsj g) (rpsj p)
rpsj (IffF' f g pf pg) = IffF' (rfsj f) (rfsj g) (rpsj pf) (rpsj pg)
rpsj (FaT' vxs f p) = FaT' vxs (rfsj f) (rpsj p)
rpsj (ExF' vxs f p) = ExF' vxs (rfsj f) (rpsj p)
rpsj (FaF' xs k f p) = FaF' xs k (rfsj f) (rpsj p)
rpsj (ExT' xs k f p) = ExT' xs k (rfsj f) (rpsj p)
rpsj (Cut' f pl pr) = Cut' (rfsj f) (rpsj pl) (rpsj pr)
rpsj (Mrk t p) = Mrk t $ rpsj p
rpsj Open' = Open'

removeMultiStepPrf :: Prf -> Prf
removeMultiStepPrf p@(Id' f) = p
removeMultiStepPrf p@(EqR' _) = p
removeMultiStepPrf p@(EqS' _ _) = p
removeMultiStepPrf p@EqT' {} = p
removeMultiStepPrf p@FunC' {} = p
removeMultiStepPrf p@RelC' {} = p
removeMultiStepPrf (NotT' f p) = NotT' f (removeMultiStepPrf p)
removeMultiStepPrf (NotF' f p) = NotF' f (removeMultiStepPrf p)

removeMultiStepPrf (OrT' ps) = OrT' $ L.map (DBF.second removeMultiStepPrf) ps
removeMultiStepPrf (AndF' ps) = AndF' $ L.map (DBF.second removeMultiStepPrf) ps

removeMultiStepPrf (AndT' _ [] p) = removeMultiStepPrf p
removeMultiStepPrf (OrF'  _ [] p) = removeMultiStepPrf p

removeMultiStepPrf (AndT' fs [g] p) = AndT' fs [g] $ removeMultiStepPrf p
removeMultiStepPrf (OrF'  fs [g] p) = OrF'  fs [g] $ removeMultiStepPrf p

removeMultiStepPrf (AndT' fs (g : gs) p) = AndT' fs [g] $ removeMultiStepPrf (AndT' fs gs p) 
removeMultiStepPrf (OrF' fs  (g : gs) p) = OrF'  fs [g] $ removeMultiStepPrf (OrF'  fs gs p) 

removeMultiStepPrf (ImpFA' f g p) = ImpFA' f g (removeMultiStepPrf p)
removeMultiStepPrf (ImpFC' f g p) = ImpFC' f g (removeMultiStepPrf p)
removeMultiStepPrf (ImpT' f g pf pg) = ImpT' f g (removeMultiStepPrf pf) (removeMultiStepPrf pg)
removeMultiStepPrf (IffTO' f g p) = IffTO' f g (removeMultiStepPrf p)
removeMultiStepPrf (IffTR' f g p) = IffTR' f g (removeMultiStepPrf p)
removeMultiStepPrf (IffF' f g pf pg) = IffF' f g (removeMultiStepPrf pf) (removeMultiStepPrf pg)
removeMultiStepPrf (FaT' vxs f p) = FaT' vxs f (removeMultiStepPrf p)
removeMultiStepPrf (ExF' vxs f p) = ExF' vxs f (removeMultiStepPrf p)
removeMultiStepPrf (FaF' xs k f p) = FaF' xs k f (removeMultiStepPrf p)
removeMultiStepPrf (ExT' xs k f p) = ExT' xs k f (removeMultiStepPrf p)
removeMultiStepPrf (Cut' f pl pr) = Cut' f (removeMultiStepPrf pl) (removeMultiStepPrf pr)
removeMultiStepPrf (Mrk t p) = Mrk t $ removeMultiStepPrf p
removeMultiStepPrf Open' = Open'

-- resj :: Stelab -> Stelab
-- resj (InfStep f p t) = InfStep f (rpsj p) t
-- resj (AoCStep xs f g p t) = AoCStep xs (rfsj f) (rfsj g) (rpsj p) t
-- resj (DefStep f g p t) = DefStep (rfsj f) (rfsj g) (rpsj p) t

-- detectSJ :: Elab -> IO ()
-- detectSJ ((ep, _, f), _, _)
--   | formSJ f = eb "single junct at EP : " 
--   | otherwise = return ()


checkStelab :: Set Form -> Stelab -> IO Form
checkStelab sq (InfStep g p nm) = do
  -- pb $ "Checking inf-stelab : " <> ft nm <> "\n"
  verify 0 sq (S.singleton g) p
  return g
checkStelab sq (DefStep f g p nm) = do
  -- pb $ "Checking def-stelab : " <> ft nm <> "\n"
  guard $ isRelD f
  verify 0 (S.singleton f) (S.singleton g) p
  return g
checkStelab sq (AoCStep xs f g p nm) = do
  -- pb $ "Checking aoc-stelab : " <> ft nm <> "\n"
  isAoC' xs f
  verify 0 (S.singleton f) (S.singleton g) p
  return g

-- stelabConc :: Stelab -> Form
-- stelabConc (InfStep g p _) = g
-- stelabConc (DefStep f g p _) = g
-- stelabConc (AoCStep xs f g p _) = g

infer :: Text -> [Form] -> Form -> IO Prf
infer "superposition" [f, g] h         = superpose f g h
infer "forward_demodulation" [f, g] h  = superpose f g h
infer "backward_demodulation" [f, g] h = superpose f g h
infer "negated_conjecture" [f] g = guard (f == g) >> return (Id' f)
infer "factoring" [f] g = efactor (Just True) f g
infer "nnf_transformation" [f] g = nnfTrans False f g
infer "ennf_transformation" [f] g = nnfTrans True f g
infer "true_and_false_elimination" [f] g = trueFalseElim f g
infer "duplicate_literal_removal" [f] g = efactor (Just True) f g
infer "equality_resolution" [f] g = efactor (Just False) f g
infer "trivial_inequality_removal" [f] g = efactor nt f g
infer "subsumption_resolution" [f, g] h = resolve f g h
infer "resolution" [f, g] h = resolve f g h
infer "definition_folding" (f : fs) g = definFold fs f g
infer "definition_unfolding" (f : fs) g = dunfold fs f g
infer "pure_predicate_removal" [f] g = removePure f g
infer "flattening" [f] g = flattening f g
infer "equality_factoring" [f] g = eqfactor f g
infer "rectify" [f] g            = rectify f g
infer "avatar_component_clause" [f] g = avatarComp f g
infer "cnf_transformation" [f] g = cnfTrans f g
infer "avatar_split_clause" (f : fs) g    = avatarSplit fs f g
infer "unused_predicate_definition_removal" [f] g = updr 0 f g
infer "avatar_contradiction_clause" [f] g = efactor (Just True) f g
infer "skolemisation" (f : fs) g = skolemize fs 0 f g
infer "usedef" [f] g = usedef f g 
infer r fs g = et $ "No inference : " <> r

unsnoc :: [a] -> Maybe ([a], a)
unsnoc [] = mzero
unsnoc [x] = return ([], x)
unsnoc (x : xs) = DBF.first (x :) <$> unsnoc xs

usedef' :: Form -> Form -> IO Prf
usedef' (Iff f g) (Or [g', Not f']) = do
  guard $ f == f' && g == g'
  return $ IffTO' f g $ impToOrNot f g  
usedef' (Iff f (Or gs)) (Or gsf) = do
  (gs', Not f') <- cast $ unsnoc gsf
  guardMsg "defniendum mismatch" $ f == f'
  guardMsg "defniens mismatch" $ gs == gs'
  return $ rDefLemma1 f gs gsf
usedef' f g 
  | f == g = return $ Id' f
  | otherwise = eb $ "Cannot use def\n" <> "f : " <> ppForm f <> "\ng : " <> ppForm g <> "\n"

usedef :: Form -> Form -> IO Prf
usedef (Fa vs f) (Fa ws g) = do 
  let (_, xs) = listPars 0 ws
  vxs <- zipM vs xs
  wxs <- zipM ws xs
  let f' = substForm vxs f 
  let g' = substForm wxs g
  p <- usedef' f' g' 
  return $ FaF' ws 0 g $ FaT' vxs f p
usedef f g = usedef' f g 

elabStep :: NTF -> Step -> IO Stelab
elabStep s (n, "file", [m], g) = do
  f <- cast (HM.lookup m s)
  -- pb $ "Formula " <> ft m <> " : " <> ppForm f <> "\n"
  -- pb $ "Formula " <> ft n <> " : " <> ppForm g <> "\n"
  p <- orig f g
  return $ InfStep g p n
elabStep _ (n, "predicate_definition_introduction", [], g) = relDef n g
elabStep _ (n, "avatar_definition", [], g) = relDef n g
elabStep s (n, "choice_axiom", [], g) = do
  (xs, f) <- normalizeAoC g
  p <- orig f g
  return $ AoCStep xs f g p n
elabStep s (n, "avatar_sat_refutation", ns, g) = do
  fs <- mapM (`lookupM` s) ns
  p <- sat fs
  return $ InfStep g p n
elabStep s (n, r, ns, g) = do
  fs <- mapM (`lookupM` s) ns
  p <- infer r fs g
  return $ InfStep g p n

stelabIO :: Bool -> (NTF, Set Form) -> Step -> IO ((NTF, Set Form), Stelab) -- todo : eliminate checking during Stelab-IO
stelabIO vb (nsq, sq) af@(n, _, _, f) = do
  when vb $ print $ "Elaborating step = " <> n
  e <- elabStep nsq af
  return ((HM.insert n f nsq, S.insert f sq), e)

stepsToStelabs :: Bool -> NTF -> Set Form -> [Step] -> IO [Stelab]
stepsToStelabs vb ntf sf stps = do
  (_, es) <- mapAccumM (stelabIO vb) (ntf, sf) stps
  return es

desingle :: Stelab -> Stelab
desingle (InfStep f p tx) = InfStep (rfsj f) (rpsj p) tx
desingle (DefStep f g p tx) = DefStep (rfsj f) (rfsj g) (rpsj p) tx
desingle (AoCStep xs f g p tx) = AoCStep xs (rfsj f) (rfsj g) (rpsj p) tx

removeMultiStep :: Stelab -> Stelab
removeMultiStep (InfStep f p tx) = InfStep f (removeMultiStepPrf p) tx
removeMultiStep (DefStep f g p tx) = DefStep f g (removeMultiStepPrf p) tx
removeMultiStep (AoCStep xs f g p tx) = AoCStep xs f g (removeMultiStepPrf p) tx

indexStelabs :: Int -> HM.Map Funct Int -> [Stelab] -> IO [Stelab]
indexStelabs k mp [] = return []
indexStelabs k mp (InfStep f p tx : slbs) = do
  slbs' <- indexStelabs k mp slbs
  return $ InfStep (indexForm mp f) (indexPrf k mp p) tx : slbs'
indexStelabs k mp (DefStep f g p tx : slbs) = do
  let r = definedRel f 
  guardMsg "Cannot re-index existing functor" $ HM.notMember r mp
  let mp' = HM.insert r k mp 
  let f' = indexForm mp' f 
  let g' = indexForm mp' g 
  let p' = indexPrf (k + 1) mp' p 
  slbs' <- indexStelabs (k + 1) mp' slbs 
  return $ DefStep f' g' p' tx : slbs'
indexStelabs k mp (AoCStep xs f g p tx : slbs) = do
  let ((k', mp'), xs') = L.mapAccumL indexAoCStep (k, mp) xs 
  let f' = indexForm mp' f
  let g' = indexForm mp' g
  let p' = indexPrf k' mp' p
  slbs' <- indexStelabs k' mp' slbs 
  return $ AoCStep xs' f' g' p' tx : slbs'

indexAoCStep :: (Int, HM.Map Funct Int) -> Term -> ((Int, HM.Map Funct Int), Term)
indexAoCStep (k, mp) (Fun (Reg tx) xs) = 
  if HM.member (Reg tx) mp
  then et "Cannot re-index existing functor"
  else ((k + 1, HM.insert (Reg tx) k mp), Fun (Idx k) xs)
indexAoCStep (k, mp) x =  error "cannot get functor text"

indexPrf :: Int -> HM.Map Funct Int -> Prf -> Prf
indexPrf k mp Open' = Open'
indexPrf k mp (Id' f) = Id' (indexForm mp f)
indexPrf k mp (EqR' x) = EqR' (indexTerm mp x)
indexPrf k mp (EqS' x y) = EqS' (indexTerm mp x) (indexTerm mp y)
indexPrf k mp (EqT' x y z) = EqT' (indexTerm mp x) (indexTerm mp y) (indexTerm mp z)
indexPrf k mp (FunC' f xs ys) = FunC' (indexFunctor mp f) (L.map (indexTerm mp) xs) (L.map (indexTerm mp) ys)
indexPrf k mp (RelC' r xs ys) = RelC' (indexFunctor mp r) (L.map (indexTerm mp) xs) (L.map (indexTerm mp) ys)
indexPrf k mp (NotT' f p) = NotT' (indexForm mp f) $ indexPrf k mp p
indexPrf k mp (NotF' f p) = NotF' (indexForm mp f) $ indexPrf k mp p
indexPrf k mp (AndT' fs gs p) = AndT' (L.map (indexForm mp) fs) (L.map (indexForm mp) gs) $ indexPrf k mp p
indexPrf k mp (OrF' fs gs p)  = OrF'  (L.map (indexForm mp) fs) (L.map (indexForm mp) gs) $ indexPrf k mp p
indexPrf k mp (OrT' fps) =  OrT'  $ L.map (bimap (indexForm mp) (indexPrf k mp)) fps
indexPrf k mp (AndF' fps) = AndF' $ L.map (bimap (indexForm mp) (indexPrf k mp)) fps
indexPrf k mp (ImpT' f g p q) = ImpT' (indexForm mp f) (indexForm mp g) (indexPrf k mp p) (indexPrf k mp q)
indexPrf k mp (ImpFA' f g p) = ImpFA' (indexForm mp f) (indexForm mp g) $ indexPrf k mp p
indexPrf k mp (ImpFC' f g p) = ImpFC' (indexForm mp f) (indexForm mp g) $ indexPrf k mp p
indexPrf k mp (IffF' f g p q) = IffF' (indexForm mp f) (indexForm mp g) (indexPrf k mp p) (indexPrf k mp q)
indexPrf k mp (IffTO' f g p) = IffTO' (indexForm mp f) (indexForm mp g) $ indexPrf k mp p
indexPrf k mp (IffTR' f g p) = IffTR' (indexForm mp f) (indexForm mp g) $ indexPrf k mp p

indexPrf k mp (FaT' vxs f p) = FaT' (L.map (DBF.second $ indexTerm mp) vxs) (indexForm mp f) $ indexPrf k mp p
indexPrf k mp (ExF' vxs f p) = ExF' (L.map (DBF.second $ indexTerm mp) vxs) (indexForm mp f) $ indexPrf k mp p

indexPrf k mp (FaF' vs m f p) =
  let (_, k', mp') = L.foldl (\ (m_, k_, mp_) _ -> (m_ + 1, k_ + 1, HM.insert (Idx m_) k_ mp_)) (m, k, mp) vs in
  FaF' vs k (indexForm mp f) $ indexPrf k' mp' p
indexPrf k mp (ExT' vs m f p) =
  let (_, k', mp') = L.foldl (\ (m_, k_, mp_) _ -> (m_ + 1, k_ + 1, HM.insert (Idx m_) k_ mp_)) (m, k, mp) vs in
  ExT' vs k (indexForm mp f) $ indexPrf k' mp' p

indexPrf k mp (Cut' f p q) = Cut' (indexForm mp f) (indexPrf k mp p) (indexPrf k mp q)
indexPrf k mp (Mrk s p) = Mrk s $ indexPrf k mp p

relabelPairsAoC :: [Term] -> Int -> [(Funct, Int)]
relabelPairsAoC [] _ = []
relabelPairsAoC (Fun f _ : xs) k = (f, k) : relabelPairsAoC xs (k + 1)
relabelPairsAoC _ _ = et "relabel-pairs-aoc"


definedRel :: Form -> Funct
definedRel (Fa _ f) = definedRel f
definedRel (Iff (Rel (Reg tx) _) _) = Reg tx
definedRel _ = et "Not a relation definition"


relabelPairs :: Int -> Int -> Int -> [(Funct, Int)]
relabelPairs 0 _ _ = []
relabelPairs l k m = (Idx k, m) : relabelPairs (l - 1) (k + 1) (m + 1)

-- relabel' :: [(Funct, Int)] -> Prf -> Prf
-- relabel' kms Open' = Open'
-- relabel' kms (Id' f) = Id' $ indexForm kms f
-- relabel' kms (EqR' x) = EqR' x
-- relabel' kms (EqS' x y) = EqS' x y
-- relabel' kms (EqT' x y z) = EqT' x y z
-- relabel' kms (FunC' f xs ys) = FunC' (indexFunctor kms f) (L.map (indexTerm kms) xs) (L.map (indexTerm kms) ys)
-- relabel' kms (RelC' r xs ys) = RelC' (indexFunctor kms r) (L.map (indexTerm kms) xs) (L.map (indexTerm kms) ys)
-- relabel' kms (NotT' f p) = NotT' (indexForm kms f) $ relabel' kms p
-- relabel' kms (NotF' f p) = NotT' (indexForm kms f) $ relabel' kms p
-- relabel' kms (OrT' gps) = OrT' $ L.map (bimap (indexForm kms) (relabel' kms)) gps
-- relabel' kms (OrF' fs gs p) = OrF'   (L.map (indexForm kms) fs) (L.map (indexForm kms) gs) $ relabel' kms p
-- relabel' kms (AndT' fs gs p) = AndT' (L.map (indexForm kms) fs) (L.map (indexForm kms) gs) $ relabel' kms p
-- relabel' kms (AndF' fps) = AndF' $ L.map (bimap (indexForm kms) (relabel' kms)) fps
-- relabel' kms (ImpT' f g p q) = ImpT' (indexForm kms f) (indexForm kms g) (relabel' kms p) (relabel' kms q)
-- relabel' kms (ImpFA' f g p) = ImpFA' (indexForm kms f) (indexForm kms g) $ relabel' kms p
-- relabel' kms (ImpFC' f g p) = ImpFC' (indexForm kms f) (indexForm kms g) $ relabel' kms p
-- relabel' kms (IffF' f g p q) = IffF' (indexForm kms f) (indexForm kms g) (relabel' kms p) (relabel' kms q)
-- relabel' kms (IffTO' f g p) = IffTO' (indexForm kms f) (indexForm kms g) $ relabel' kms p
-- relabel' kms (IffTR' f g p) = IffTR' (indexForm kms f) (indexForm kms g) $ relabel' kms p
-- relabel' kms (FaT' vxs f p) = FaT' (L.map (DBF.second $ indexTerm kms) vxs) (indexForm kms f) $ relabel' kms p
-- relabel' kms (FaF' vs m f p) = FaF' vs m (indexForm kms f) (relabel' kms p)
-- relabel' kms (ExT' vs m f p) = ExT' vs m (indexForm kms f) (relabel' kms p)
-- relabel' kms (ExF' vxs f p) = ExF' vxs (indexForm kms f) $ relabel' kms p
-- -- relabel' kms (AoC' xs f p) = AoC' (L.map (indexTerm kms) xs) (indexForm kms f) (relabel' kms p)
-- -- relabel' kms (RelD' f p) = RelD' (indexForm kms f) (relabel' kms p)
-- relabel' kms (Cut' f p0 p1) = Cut' (indexForm kms f) (relabel' kms p0) (relabel' kms p1)
-- relabel' kms (Mrk s p) = Mrk s $ relabel' kms p

indexForm :: HM.Map Funct Int -> Form -> Form
indexForm kms (Eq x y) = Eq (indexTerm kms x) (indexTerm kms y)
indexForm kms (Rel r xs) = Rel (indexFunctor kms r) $ L.map (indexTerm kms) xs
indexForm kms (Not f) = Not $ indexForm kms f
indexForm kms (Or fs) = Or $ L.map (indexForm kms) fs
indexForm kms (And fs) = And $ L.map (indexForm kms) fs
indexForm kms (Imp f g) = Imp (indexForm kms f) (indexForm kms g)
indexForm kms (Iff f g) = Iff (indexForm kms f) (indexForm kms g)
indexForm kms (Fa vs f) = Fa vs $ indexForm kms f
indexForm kms (Ex vs f) = Ex vs $ indexForm kms f

indexTerm :: HM.Map Funct Int -> Term -> Term
indexTerm _ v@(Var _) = v
indexTerm kms (Fun f xs) = Fun (indexFunctor kms f) $ L.map (indexTerm kms) xs

indexFunctor :: HM.Map Funct Int -> Funct -> Funct
indexFunctor mp f = 
  case HM.lookup f mp of 
    Just k -> Idx k 
    _ -> f

-- type Loc = (Text, [Int], Int)
type Loc = (Text, [(Int, Int)], Int)

ppFork :: (Int, Int) -> Builder
ppFork (k, m) = ppMarkHex k <> ppMarkHex m

ppLoc :: Loc -> Builder
ppLoc (tx, ks, k) = ft tx <> bconcat (L.map ppFork $ L.reverse ks) <> ppMarkHex k

locText :: Loc -> Text
locText = tlt . ppLoc

extLoc :: Loc -> Int -> Loc
extLoc (tx, ks, k) 0 = (tx, ks, k + 1)
extLoc (tx, ks, k) m = (tx, (k, m) : ks, 0)

range :: Int -> Int -> [Int]
range _ 0 = []
range k m = k : range (k + 1) (m - 1)

stitch :: SFTN -> NodeInfo -> [Stelab] -> IO Proof
stitch sftn ni@(nm, True, Or []) [] = return (OrT_ ni nm [])
stitch _ _ [] = error "Last signed formula of branch is not a T-bot"
stitch sftn ni (InfStep g prf cmt : slbs) = do 
  let loc = (cmt, [], 0)
  proofL <- deliteral' sftn loc (False, g) prf
  proofR <- stitch (HM.insert (True, g) cmt sftn) (cmt, True, g) slbs
  return $ Cut_ ni proofL proofR
stitch sftn ni (DefStep f g p cmt : slbs) = do 
  let loc = (cmt, [], 0)
  let loc' = extLoc loc 0
  let sftn' = HM.insert (True, f) (tlt $ ppLoc loc) sftn
  pf <- deliteral' sftn' loc' (False, g) p
  pt <- stitch (HM.insert (True, g) cmt sftn') (cmt, True, g) slbs
  return $ RelD_ ni $ Cut_ (tlt (ppLoc loc), True, f) pf pt

stitch sftn ni (AoCStep xs f g prf_g cmt : slbs) = do 
  (vs, fa) <- breakAoC f
  nxfs <- singleAoCs 0 (cmt <> "_AoCs_") xs vs fa
  let locf = (cmt <> "_AoC", [], 0)
  let nmf = cmt <> "_AoC"
  let locg = (cmt, [], 0)
  let nmg = cmt
  prf_f <- proveAoC nxfs f
  let sftn_fs = foldl (\ sftn_ (nm_, _, f_) -> HM.insert (True, f_) nm_ sftn_) sftn nxfs
  pf <- deliteral' sftn_fs locf (False, f) prf_f
  let sftn_f = HM.insert (True, f) nmf sftn
  pg <- deliteral' sftn_f locg (False, g) prf_g
  let sftn_fg = HM.insert (True, g) nmg sftn_f
  pt <- stitch sftn_fg (cmt, True, g) slbs
  return $ stitchAoCs ni nxfs pf (Cut_ (nmf, True, f) pg pt)

stitchAoCs :: NodeInfo -> [(Text, Term, Form)] -> Proof -> Proof -> Proof
stitchAoCs ni [] pf pr = Cut_ ni pf pr 
stitchAoCs ni ((nm, x, f) : nxfs) pf pr = 
  let p = stitchAoCs (nm, True, f) nxfs pf pr in
  AoC_ ni x p 

lastSkolemIdx :: [(Text, Term, Form)] -> IO Int
lastSkolemIdx [] = mzero
lastSkolemIdx [(_, Fun (Idx k) _, _)] = return k
lastSkolemIdx [(_, _, _)] = mzero
lastSkolemIdx (_ : nxfs) = lastSkolemIdx nxfs

-- f0 ... fn, fa |- fc
proveAoC' :: [(Text, Term)] -> [(Text, Term, Form)] -> Form -> Form -> IO Prf
proveAoC' _ [] fa fc = do 
  guard $ fa == fc 
  return $ Id' fa
proveAoC' [] ((_, _, Imp fa' fc') : nxfs) fa fc = do
  guard $ fa' == fa
  p <- proveAoC' [] nxfs fc' fc
  return $ ImpT' fa' fc' (Id' fa) p
proveAoC' vxs@(_ : _) ((_, _, Fa vs f) : nxfs) fa fc = do
  guard $ vs == L.map fst vxs 
  (Imp fa' fc') <- return $ substForm vxs f
  guard $ fa' == fa
  p <- proveAoC' vxs nxfs fc' fc
  return $ FaT' vxs f $ ImpT' fa' fc' (Id' fa) p
proveAoC' _ _ _ _ = mzero

proveAoC :: [(Text, Term, Form)] -> Form -> IO Prf
proveAoC nxfs (Fa vs f) = do 
  k <- lastSkolemIdx nxfs
  let (_, vxs) = varPars (k + 1) vs
  (Imp fa fc) <- return $ substForm vxs f
  p <- proveAoC' vxs nxfs fa fc
  return $ FaF' vs (k + 1) f (impFAC fa fc p)
proveAoC nxfs (Imp fa fc) = do
  p <- proveAoC' [] nxfs fa fc
  return $ impFAC fa fc p

proveAoC _ _ = mzero


-- stitch :: SFTN -> NodeInfo -> [Stelab] -> IO Proof


breakAoC :: Form -> IO ([Text], Form)
breakAoC (Fa vs (Imp (Ex ws f) _)) = return (vs, Ex ws f)
breakAoC (Imp (Ex ws f) _) = return ([], Ex ws f)
breakAoC _ = mzero

singleAoCs :: Int -> Text -> [Term] -> [Text] -> Form -> IO [(Text, Term, Form)]
singleAoCs k nm [] vs _ = mzero

singleAoCs k nm [x] [] (Ex [w] f) = do 
  let nmk = nm <> tlt (ppInt k)
  let f' = substForm [(w, x)] f
  return [(nmk, x, Imp (Ex [w] f) f')]

singleAoCs k nm [x] vs (Ex [w] f) = do 
  let nmk = nm <> tlt (ppInt k)
  let f' = substForm [(w, x)] f
  return [(nmk, x, Fa vs (Imp (Ex [w] f) f'))]

singleAoCs k nm (x : xs) [] (Ex (w : ws) f) = do 
  let nmk = nm <> tlt (ppInt k)
  let f' = substForm [(w, x)] (Ex ws f)
  l <- singleAoCs (k + 1) nm xs [] f'
  return $ (nmk, x, Imp (Ex (w : ws) f) f') : l

singleAoCs k nm (x : xs) vs (Ex (w : ws) f) = do 
  let nmk = nm <> tlt (ppInt k)
  let f' = substForm [(w, x)] (Ex ws f)
  l <- singleAoCs (k + 1) nm xs vs f'
  return $ (nmk, x, Fa vs (Imp (Ex (w : ws) f) f')) : l

singleAoCs _ _ _ _ _ = mzero

deliteral' :: SFTN -> Loc -> (Bool, Form) -> Prf -> IO Proof
deliteral' sftn loc (b, f) prf = do
  let sftn' = HM.insert (b, f) (locText loc) sftn 

  -- pt "\n-----------------------------------------------------------\n"
  -- pt "Branch after insert :\n"
  -- pb $ ppInter "\n" $ L.map (\ (sf_, nm_) ->  ppSignForm sf_ <> " ----- " <> ft nm_ <> "\n") $ HM.toList sftn'

  -- pt "\n-----------------------------------------------------------\n"
  -- pb "Proof :\n"
  -- pb $ ppPrf 5 prf
  -- pt "\n-----------------------------------------------------------\n\n\n\n"

  deliteral sftn' loc (b, f) prf

deliteral :: SFTN -> Loc -> (Bool, Form) -> Prf -> IO Proof
deliteral sftn loc (b, h) Open' = return $ Open_ (locText loc, b, h) 

deliteral sftn loc (b, h) (Id' f) = do
  nt <- cast $ HM.lookup (True, f)  sftn 
  nf <- cast $ HM.lookup (False, f) sftn 
  return $ Id_ (locText loc, b, h) nt nf

deliteral sftn loc (b, h) (EqR' x) = do
  nm <- cast $ HM.lookup (False, Eq x x) sftn 
  return $ EqR_ (locText loc, b, h) nm
deliteral sftn loc (b, h) (EqS' x y) = do
  nt <- cast $ HM.lookup (True, Eq x y) sftn 
  nf <- cast $ HM.lookup (False, Eq y x) sftn 
  return $ EqS_ (locText loc, b, h) nt nf
deliteral sftn loc (b, h) (EqT' x y z) = do
  nxy <- cast $ HM.lookup (True, Eq x y) sftn 
  nyz <- cast $ HM.lookup (True, Eq y z) sftn 
  nxz <- cast $ HM.lookup (False, Eq x z) sftn 
  return $ EqT_ (locText loc, b, h) nxy nyz nxz
deliteral sftn loc (b, h) (FunC' f xs ys) = do
  xys <- zipM xs ys
  let eqns = L.map ((True,) . uncurry Eq) xys
  nms <- cast $ mapM (`HM.lookup` sftn) eqns
  nm <- cast $ HM.lookup (False, Fun f xs === Fun f ys) sftn 
  return $ FunC_ (locText loc, b, h) nms nm
deliteral sftn loc (b, h) (RelC' r xs ys) = do
  xys <- zipM xs ys
  let eqns = L.map ((True,) . uncurry Eq) xys
  nms <- cast $ mapM (`HM.lookup` sftn) eqns
  nt <- cast $ HM.lookup (True, Rel r xs) sftn 
  nf <- cast $ HM.lookup (False, Rel r ys) sftn 
  return $ RelC_ (locText loc, b, h) nms nt nf

deliteral sftn loc (b, h) (NotT' f p) = do
  let loc' = extLoc loc 0
  nm <- cast $ HM.lookup (True, Not f) sftn 
  p' <- deliteral' sftn loc' (False, f) p 
  return $ NotT_ (locText loc, b, h) nm p'

deliteral sftn loc (b, h) (NotF' f p) = do
  let loc' = extLoc loc 0
  nm <- cast $ HM.lookup (False, Not f) sftn 
  p' <- deliteral' sftn loc' (True, f) p 
  return $ NotF_ (locText loc, b, h) nm p'
  
deliteral sftn loc (b, h) (OrT' fps) = do
  let (fs, _) = unzip fps
  nm <- cast $ HM.lookup  (True, Or fs) sftn 
  let ks = range 0 $ L.length fps
  ps' <- mapM2 (\ k_ (f_, p_) -> deliteral' sftn (extLoc loc k_) (True, f_) p_) ks fps
  return $ OrT_ (locText loc, b, h) nm ps'

deliteral sftn loc (b, h) (OrF' fs [f] p) = do
  let loc' = extLoc loc 0
  nm <- cast $ HM.lookup (False, Or fs) sftn 
  p' <- deliteral' sftn loc' (False, f) p 
  k <- cast $ elemIndex f fs
  return $ OrF_ (locText loc, b, h) nm k p'
deliteral sftn loc (b, h) (OrF' fs gs p) = eb $ "single residue : " <> ppForm (Or gs)

deliteral sftn loc (b, h) (AndT' fs [f] p) = do
  let loc' = extLoc loc 0
  nm <- cast $ HM.lookup (True, And fs) sftn 
  p' <- deliteral' sftn loc' (True, f) p 
  k <- cast $ elemIndex f fs
  return $ AndT_ (locText loc, b, h) nm k p'
deliteral sftn loc (b, h) (AndT' fs gs p) = eb $ "single residue : " <> ppForm (And gs)

deliteral sftn loc (b, h) (AndF' fps) = do
  let (fs, _) = unzip fps
  let ks = range 0 $ L.length fps
  nm <- cast $ HM.lookup  (False, And fs) sftn 
  ps' <- mapM2 (\ k_ (f_, p_) -> deliteral' sftn (extLoc loc k_) (False, f_) p_) ks fps
  return $ AndF_ (locText loc, b, h) nm ps'

deliteral sftn loc (b, h) (ImpT' f g p q) = do
  nm <- cast $ HM.lookup (True, Imp f g) sftn 
  p' <- deliteral' sftn (extLoc loc 0) (False, f) p 
  q' <- deliteral' sftn (extLoc loc 1) (True, g) q 
  return $ ImpT_ (locText loc, b, h) nm p' q'

deliteral sftn loc (b, h) (ImpFA' f g p) = do
  nm <- cast $ HM.lookup  (False, Imp f g) sftn 
  p' <- deliteral' sftn (extLoc loc 0) (True, f) p 
  return $ ImpFA_ (locText loc, b, h) nm p' 

deliteral sftn loc (b, h) (ImpFC' f g p) = do
  nm <- cast $ HM.lookup  (False, Imp f g) sftn 
  p' <- deliteral' sftn (extLoc loc 0) (False, g) p 
  return $ ImpFC_ (locText loc, b, h) nm p' 

deliteral sftn loc (b, h) (IffF' f g p q) = do
  nm <- cast $ HM.lookup (False, Iff f g) sftn 
  p' <- deliteral' sftn (extLoc loc 0) (False, Imp f g) p 
  q' <- deliteral' sftn (extLoc loc 1) (False, Imp g f) q 
  return $ IffF_ (locText loc, b, h) nm p' q'

deliteral sftn loc (b, h) (IffTO' f g p) = do
  nm <- cast $ HM.lookup (True, Iff f g) sftn 
  p' <- deliteral' sftn (extLoc loc 0) (True, Imp f g) p 
  return $ IffTO_ (locText loc, b, h) nm p' 

deliteral sftn loc (b, h) (IffTR' f g p) = do
  nm <- cast $ HM.lookup (True, Iff f g) sftn 
  p' <- deliteral' sftn (extLoc loc 0) (True, Imp g f) p 
  return $ IffTR_ (locText loc, b, h) nm p' 

deliteral sftn loc (b, h) (FaT' vxs f p) = do
  let (vs, xs) = unzip vxs 
  nm <- cast $ HM.lookup (True, Fa vs f) sftn 
  let f' = substForm vxs f
  p' <- deliteral' sftn (extLoc loc 0) (True, f') p 
  return $ FaT_ (locText loc, b, h) nm xs p'

deliteral sftn loc (b, h) (FaF' vs m f p) = do
  nm <- cast $ HM.lookup (False, Fa vs f) sftn -- <> eb ("Cannot find hyp:\n" <> ppSignForm (False, Fa vs f)) 
  let (_, vxs) = varPars m vs 
  let f' = substForm vxs f
  p' <- deliteral' sftn (extLoc loc 0) (False, f') p 
  return $ FaF_ (locText loc, b, h) nm m p'

deliteral sftn loc (b, h) (ExT' vs m f p) = do
  nm <- cast $ HM.lookup (True, Ex vs f) sftn 
  let (_, vxs) = varPars m vs 
  let f' = substForm vxs f
  p' <- deliteral' sftn (extLoc loc 0) (True, f') p 
  return $ ExT_ (locText loc, b, h) nm m p'

deliteral sftn loc (b, h) (ExF' vxs f p) = do
  let (vs, xs) = unzip vxs 
  nm <- cast $ HM.lookup (False, Ex vs f) sftn 
  let f' = substForm vxs f
  p' <- deliteral' sftn (extLoc loc 0) (False, f') p 
  return $ ExF_ (locText loc, b, h) nm xs p'

deliteral sftn loc (b, h) (Cut' f p q) = do
  p' <- deliteral' sftn (extLoc loc 1) (False, f) p 
  q' <- deliteral' sftn (extLoc loc 0) (True, f) q 
  return $ Cut_ (locText loc, b, h) p' q'
  
deliteral sftn loc (b, h) (Mrk s p) = deliteral sftn loc (b, h) p

linearize :: Proof -> [Elab]
linearize (Id_ ni nt nf) = [(ni, Id nt nf, Nothing)]
linearize (Cut_ ni p q) = (ni, Cut (proofRN p) (proofRN q), Nothing) : linearize p ++ linearize q
linearize (FunC_ ni xs nm) = [(ni, FunC xs nm, Nothing)]
linearize (RelC_ ni xs nt nf) = [(ni, RelC xs nt nf, Nothing)]
linearize (EqR_ ni nm) = [(ni, EqR nm, Nothing)]
linearize (EqS_ ni nt nf) = [(ni, EqS nt nf, Nothing)]
linearize (EqT_ ni nxy nyz nxz) = [(ni, EqT nxy nyz nxz, Nothing)]
linearize (NotT_ ni nm p) = (ni, NotT nm (proofRN p), Nothing) : linearize p
linearize (NotF_ ni nm p) = (ni, NotF nm (proofRN p), Nothing) : linearize p
linearize (OrT_ ni nm ps) = (ni, OrT nm (L.map proofRN ps), Nothing) : L.concatMap linearize ps
linearize (OrF_ ni nm k p) = (ni, OrF nm k (proofRN p), Nothing) : linearize p
linearize (AndT_ ni nm k p) = (ni, AndT nm k (proofRN p), Nothing) : linearize p
linearize (AndF_ ni nm ps) = (ni, AndF nm (L.map proofRN ps), Nothing) : L.concatMap linearize ps
linearize (ImpT_ ni nm p q) = (ni, ImpT nm (proofRN p) (proofRN q), Nothing) : linearize p ++ linearize q
linearize (ImpFA_ ni nm p) = (ni, ImpFA nm (proofRN p), Nothing) : linearize p
linearize (ImpFC_ ni nm p) = (ni, ImpFC nm (proofRN p), Nothing) : linearize p
linearize (IffTO_ ni nm p) = (ni, IffTO nm (proofRN p), Nothing) : linearize p
linearize (IffTR_ ni nm p) = (ni, IffTR nm (proofRN p), Nothing) : linearize p
linearize (IffF_ ni nm p q) = (ni, IffF nm (proofRN p) (proofRN q), Nothing) : linearize p ++ linearize q
linearize (FaT_ ni nm xs p) = (ni, FaT nm xs (proofRN p), Nothing) : linearize p
linearize (FaF_ ni nm k p) = (ni, FaF nm k (proofRN p), Nothing) : linearize p
linearize (ExT_ ni nm k p) = (ni, ExT nm k (proofRN p), Nothing) : linearize p
linearize (ExF_ ni nm xs p) = (ni, ExF nm xs (proofRN p), Nothing) : linearize p
linearize (RelD_ ni p) = (ni, RelD (proofRN p), Nothing) : linearize p
linearize (AoC_ ni xs p) = (ni, AoC xs (proofRN p), Nothing) : linearize p
linearize (Open_ ni) = [(ni, Open, Nothing)]

checkStelabs :: Set Form -> [Stelab] -> IO ()
checkStelabs sf [] = return ()
checkStelabs sf (slb : slbs) = do 
  g <- checkStelab sf slb 
  let sf' = S.insert g sf 
  checkStelabs sf' slbs

elab :: Bool -> NTF -> Set Form -> SFTN -> [Step] -> IO Proof  -- [Elab]
elab vb ntf sf ftn stps = do
  slbs <- stepsToStelabs vb ntf sf stps
  -- checkStelabs sf slbs
  let slbs' = L.map (removeMultiStep . desingle) slbs
  -- checkStelabs sf slbs'
  slbs'' <- indexStelabs 0 HM.empty slbs'
  -- checkStelabs sf slbs''
  stitch ftn ("root", True, top) slbs''
