{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Elab where

import Types
import LocalTypes
import Basic
import PP 
import Prove 
import Lem (impFAC, impToOrNot, rDefLemma1)
import Sat (sat)
-- import Check (isRelD, verify)

import Data.List as L (all, map, foldl, length, reverse, findIndex, concatMap, mapAccumL, elemIndex)
import Data.Map as HM (insert, lookup, Map, empty, toList, member, notMember, keys)
import Data.Set as S (Set, insert, singleton, toList, fromList, member, map)
import Data.ByteString.Builder (Builder)
import Control.Monad as M ( guard, MonadPlus(mzero), foldM, foldM_, when )
import Control.Monad.Fail as MF (MonadFail, fail)
import Control.Applicative ( Alternative((<|>)) )
import Data.Bifunctor as DBF (first, second, bimap)
import Norm (fltn)
import GHC.Stack (pushCallStack)
import Data.ByteString.Conversion (toByteString', runBuilder)
import Debug.Trace (trace)

rfsj :: Form -> Form
rfsj Top = Top
rfsj Bot = Bot
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
rpsj TopF' = TopF'
rpsj BotT' = BotT'
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
    [g] -> if f == g then rpsj p else error "rpsj-and-lft-0"
    _ -> error "rpsj-and-lft-1"
rpsj (AndT' fs gs p) = AndT' (L.map rfsj fs) (L.map rfsj gs) (rpsj p)
rpsj (OrF' [f] gs p) =
  case gs of
    [g] -> if f == g then rpsj p else error "rpsj-or-rgt-0"
    _ -> error "rpsj-or-rgt-1"
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
rpsj (RelD' f p) = RelD' f (rpsj p)
rpsj (AoC' x f p) = AoC' x f (rpsj p)
rpsj (Mrk t p) = Mrk t $ rpsj p
rpsj Open' = Open'

removeMultiStepPrf :: Prf -> Prf
removeMultiStepPrf p@(Id' f) = p
removeMultiStepPrf p@TopF' = p
removeMultiStepPrf p@BotT' = p
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
removeMultiStepPrf (RelD' f p) = RelD' f (removeMultiStepPrf p)
removeMultiStepPrf (AoC' x f p) = AoC' x f (removeMultiStepPrf p)
removeMultiStepPrf (Mrk t p) = Mrk t $ removeMultiStepPrf p
removeMultiStepPrf Open' = Open'

-- resj :: Stelab -> Stelab
-- resj (InfStep f p t) = InfStep f (rpsj p) t
-- resj (AoCStep xs f g p t) = AoCStep xs (rfsj f) (rfsj g) (rpsj p) t
-- resj (DefStep f g p t) = DefStep (rfsj f) (rfsj g) (rpsj p) t

-- detectSJ :: Elab -> IO ()
-- detectSJ ((ep, _, f), _, _)
--   | formSJ f = error "single junct at EP : " 
--   | otherwise = return ()


checkStelab :: Set Form -> Stelab -> IO Form
checkStelab sq (InfStep g p nm) = do
  pbd $ "Checking inf-stelab : " <> ft nm <> "\n"
  verify 0 sq (S.singleton g) p
  return g
checkStelab sq (DefStep f g p nm) = do
  pbd $ "Checking def-stelab : " <> ft nm <> "\n"
  guard $ isRelD f
  verify 0 (S.singleton f) (S.singleton g) p
  return g
checkStelab sq (AoCStep xs f g p nm) = do
  pbd $ "Checking aoc-stelab : " <> ft nm <> "\n"
  pbd $ "AoC = " <> ppForm f <> "\n"
  isAoC' xs f
  verify 0 (S.singleton f) (S.singleton g) p
  return g

-- stelabConc :: Stelab -> Form
-- stelabConc (InfStep g p _) = g
-- stelabConc (DefStep f g p _) = g
-- stelabConc (AoCStep xs f g p _) = g

infer :: BS -> [Form] -> Form -> IO Prf
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
infer r fs g = error $ show $ "No inference : " <> r

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
  | otherwise = error $ show $ "Cannot use def\n" <> "f : " <> ppForm f <> "\ng : " <> ppForm g <> "\n"

usedef :: Form -> Form -> IO Prf
usedef (Fa vs f) (Fa ws g) = do 
  let (_, xs) = listPars 0 ws
  let ks = rangeOver 0 ws
  let xs = L.map par ks
  f' <- substitute vs xs f 
  g' <- substitute ws xs g
  p <- usedef' f' g' 
  vxs <- zipM vs xs
  return $ FaF' ws ks g $ FaT' vxs f p
usedef f g = usedef' f g 

elabStep :: Prob -> Step -> IO Stelab
elabStep s (n, "file", [m], g) = do
  f <- cast (HM.lookup m s)
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

stelabIO :: Bool -> Prob -> Step -> IO (Prob, Stelab) -- todo : eliminate checking during Stelab-IO
stelabIO vb tptp af@(n, _, _, f) = do
  when vb $ print $ "Elaborating step = " <> n
  (HM.insert n f tptp,) <$> elabStep tptp af

stepsToStelabs :: Bool -> Prob -> [Step] -> IO [Stelab]
stepsToStelabs vb tptp stps = snd <$> mapAccumM (stelabIO vb) tptp stps

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
  then error "Cannot re-index existing functor"
  else ((k + 1, HM.insert (Reg tx) k mp), Fun (Idx k) xs)
indexAoCStep (k, mp) x =  error "cannot get functor BS"

indexPrf :: Int -> HM.Map Funct Int -> Prf -> Prf
indexPrf k mp Open' = Open'
indexPrf k mp TopF' = TopF'
indexPrf k mp BotT' = BotT'
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
indexPrf k mp (FaF' vs ms f p) =
  let (mp', ms') = mapAccumL (\ mp_ m_ -> (HM.insert (Idx m_) (m_ + k) mp_, m_ + k)) mp ms in
  FaF' vs ms' (indexForm mp f) $ indexPrf (maximum ms' + 1) mp' p
indexPrf k mp (ExT' vs ms f p) =
  let (mp', ms') = mapAccumL (\ mp_ m_ -> (HM.insert (Idx m_) (m_ + k) mp_, m_ + k)) mp ms in
  ExT' vs ms' (indexForm mp f) $ indexPrf (maximum ms' + 1) mp' p
indexPrf k mp (Cut' f p q) = Cut' (indexForm mp f) (indexPrf k mp p) (indexPrf k mp q)
indexPrf k mp (RelD' f p) = error "unexpected indexing of a RelD proof"
indexPrf k mp (AoC' _ _ p) = error "unexpected indexing of a AoC proof"
indexPrf k mp (Mrk s p) = Mrk s $ indexPrf k mp p

relabelPairsAoC :: [Term] -> Int -> [(Funct, Int)]
relabelPairsAoC [] _ = []
relabelPairsAoC (Fun f _ : xs) k = (f, k) : relabelPairsAoC xs (k + 1)
relabelPairsAoC _ _ = error "relabel-pairs-aoc"


definedRel :: Form -> Funct
definedRel (Fa _ f) = definedRel f
definedRel (Iff (Rel (Reg tx) _) _) = Reg tx
definedRel _ = error "Not a relation definition"

relabelPairs :: Int -> Int -> Int -> [(Funct, Int)]
relabelPairs 0 _ _ = []
relabelPairs l k m = (Idx k, m) : relabelPairs (l - 1) (k + 1) (m + 1)

indexForm :: HM.Map Funct Int -> Form -> Form
indexForm kms Top = Top
indexForm kms Bot = Bot
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

type Loc = (BS, [(Int, Int)], Int)

ppFork :: (Int, Int) -> Builder
ppFork (k, m) = ppMarkHex k <> ppMarkHex m

ppLoc :: Loc -> Builder
ppLoc (tx, ks, k) = ft tx <> bconcat (L.map ppFork $ L.reverse ks) <> ppMarkHex k

locBS :: Int -> BS
locBS k = toByteString' $ "e" <> ppInt k

extLoc :: Loc -> Int -> Loc
extLoc (tx, ks, k) 0 = (tx, ks, k + 1)
extLoc (tx, ks, k) m = (tx, (k, m) : ks, 0)

range :: Int -> Int -> [Int]
range _ 0 = []
range k m = k : range (k + 1) (m - 1)

stitch :: [Stelab] -> IO Prf
-- stitch _ ni@(nm, _, _) _ | trace ("stitching = " ++ bs2str nm) False = undefined 
stitch [] = return BotT'
stitch (InfStep g prf cmt : slbs) = Cut' g prf <$> stitch slbs
stitch (DefStep f g prf _ : slbs) = RelD' f . Cut' g prf <$> stitch slbs
stitch (AoCStep xs f g prf_g cmt : slbs) = do 
  (vs, fa) <- breakAoC f
  xfs <- singleAoCs xs vs fa
  prf_f <- proveAoC xfs f
  -- let sftn_fs = foldl (\ sftn_ (nm_, _, f_) -> HM.insert (True, f_) nm_ sftn_) sftn nxfs
  -- pf <- deliteral' sftn_fs locf (False, f) prf_f
  -- let sftn_f = HM.insert (True, f) nmf sftn
  -- pg <- deliteral' sftn_f locg (False, g) prf_g
  -- let sftn_fg = HM.insert (True, g) nmg sftn_f
  prf <- stitch slbs
  return $ stitchAoCs xfs f prf_f (Cut' g prf_g prf)

stitchAoCs :: [(Term, Form)] -> Form -> Prf -> Prf -> Prf
stitchAoCs [] f pf pr = 
  Cut' f pf pr 
stitchAoCs ((x, f) : xfs) f' pf pr = 
  let p = stitchAoCs xfs f' pf pr in
  AoC' x f p 

lastSkolemIdx :: [(Term, Form)] -> IO Int
lastSkolemIdx [] = mzero
lastSkolemIdx [(Fun (Idx k) _, _)] = return k
lastSkolemIdx [(_, _)] = mzero
lastSkolemIdx (_ : nxfs) = lastSkolemIdx nxfs

-- f0 ... fn, fa |- fc
proveAoC' :: [(BS, Term)] -> [(Term, Form)] -> Form -> Form -> IO Prf
proveAoC' _ [] fa fc = do 
  guard $ fa == fc 
  return $ Id' fa
proveAoC' [] ((_, Imp fa' fc') : nxfs) fa fc = do
  guard $ fa' == fa
  p <- proveAoC' [] nxfs fc' fc
  return $ ImpT' fa' fc' (Id' fa) p
proveAoC' vxs@(_ : _) ((_, Fa vs f) : nxfs) fa fc = do
  guard $ vs == L.map fst vxs 
  (Imp fa' fc') <- return $ substForm vxs f
  guard $ fa' == fa
  p <- proveAoC' vxs nxfs fc' fc
  return $ FaT' vxs f $ ImpT' fa' fc' (Id' fa) p
proveAoC' _ _ _ _ = mzero

proveAoC :: [(Term, Form)] -> Form -> IO Prf
proveAoC xfs (Fa vs f) = do 
  k <- lastSkolemIdx xfs
  let (_, vxs) = varPars (k + 1) vs
  let ks = rangeOver (k + 1) vs 
  let xs = L.map par ks
  (Imp fa fc) <- substitute vs xs f
  p <- proveAoC' vxs xfs fa fc
  return $ FaF' vs ks f (impFAC fa fc p)
proveAoC nxfs (Imp fa fc) = do
  p <- proveAoC' [] nxfs fa fc
  return $ impFAC fa fc p
proveAoC _ _ = mzero

breakAoC :: Form -> IO ([BS], Form)
breakAoC (Fa vs (Imp (Ex ws f) _)) = return (vs, Ex ws f)
breakAoC (Imp (Ex ws f) _) = return ([], Ex ws f)
breakAoC _ = mzero

singleAoCs :: [Term] -> [BS] -> Form -> IO [(Term, Form)]
singleAoCs [] vs _ = mzero
singleAoCs [x] [] (Ex [w] f) = do 
  let f' = substForm [(w, x)] f
  return [(x, Imp (Ex [w] f) f')]
singleAoCs [x] vs (Ex [w] f) = do 
  let f' = substForm [(w, x)] f
  return [(x, Fa vs (Imp (Ex [w] f) f'))]
singleAoCs (x : xs) [] (Ex (w : ws) f) = do 
  let f' = substForm [(w, x)] (Ex ws f)
  l <- singleAoCs xs [] f'
  return $ (x, Imp (Ex (w : ws) f) f') : l
singleAoCs (x : xs) vs (Ex (w : ws) f) = do 
  let f' = substForm [(w, x)] (Ex ws f)
  l <- singleAoCs xs vs f'
  return $ (x, Fa vs (Imp (Ex (w : ws) f) f')) : l
singleAoCs _ _ _ = mzero

deliteral' :: Invranch -> Int -> Bool -> Form -> Prf -> IO (Proof, Int)
deliteral' sftn loc b f prf = do
  let sftn' = HM.insert (b, f) (locBS loc) sftn 
  deliteral sftn' loc b f prf

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

deliteral :: Invranch -> Int -> Bool -> Form -> Prf -> IO (Proof, Int)
deliteral sftn loc b h Open' = return (Open_ (locBS loc, b, h) , loc + 1)
deliteral sftn loc b h TopF' = do
  nm <- cast $ HM.lookup (False, Top) sftn 
  return (TopF_ (locBS loc, b, h) nm, loc + 1)
deliteral sftn loc b h BotT' = do
  nm <- cast $ HM.lookup (True, Bot) sftn 
  return (BotT_ (locBS loc, b, h) nm, loc + 1)
deliteral sftn loc b h (Id' f) = do
  nt <- cast $ HM.lookup (True, f)  sftn 
  nf <- cast $ HM.lookup (False, f) sftn 
  return (Id_ (locBS loc, b, h) nt nf, loc + 1)
deliteral sftn loc b h (EqR' x) = do
  nm <- cast $ HM.lookup (False, Eq x x) sftn 
  return (EqR_ (locBS loc, b, h) nm, loc + 1)
deliteral sftn loc b h (EqS' x y) = do
  nt <- cast $ HM.lookup (True, Eq x y) sftn 
  nf <- cast $ HM.lookup (False, Eq y x) sftn 
  return (EqS_ (locBS loc, b, h) nt nf, loc + 1)
deliteral sftn loc b h (EqT' x y z) = do
  nxy <- cast $ HM.lookup (True, Eq x y) sftn 
  nyz <- cast $ HM.lookup (True, Eq y z) sftn 
  nxz <- cast $ HM.lookup (False, Eq x z) sftn 
  return (EqT_ (locBS loc, b, h) nxy nyz nxz, loc + 1)
deliteral sftn loc b h (FunC' f xs ys) = do
  xys <- zipM xs ys
  let eqns = L.map ((True,) . uncurry Eq) xys
  nms <- cast $ mapM (`HM.lookup` sftn) eqns
  nm <- cast $ HM.lookup (False, Fun f xs === Fun f ys) sftn 
  return (FunC_ (locBS loc, b, h) nms nm, loc + 1)
deliteral sftn loc b h (RelC' r xs ys) = do
  xys <- zipM xs ys
  let eqns = L.map ((True,) . uncurry Eq) xys
  nms <- cast $ mapM (`HM.lookup` sftn) eqns
  nt <- cast $ HM.lookup (True, Rel r xs) sftn 
  nf <- cast $ HM.lookup (False, Rel r ys) sftn 
  return (RelC_ (locBS loc, b, h) nms nt nf, loc + 1)
deliteral sftn loc b h (NotT' f p) = do
  nm <- cast $ HM.lookup (True, Not f) sftn 
  (p', loc') <- deliteral' sftn (loc + 1) False f p 
  return (NotT_ (locBS loc, b, h) nm p', loc')
deliteral sftn loc b h (NotF' f p) = do
  nm <- cast $ HM.lookup (False, Not f) sftn 
  (p', loc') <- deliteral' sftn (loc + 1) True f p 
  return (NotF_ (locBS loc, b, h) nm p', loc') -- <$> deliteral' sftn (loc + 1) True f p 
deliteral sftn loc b h (OrT' fps) = do
  let (fs, _) = unzip fps
  nm <- cast $ HM.lookup  (True, Or fs) sftn 
  (loc', ps') <- mapAccumM (\ loc_ (f_, p_) -> swap <$> deliteral' sftn loc_ True f_ p_) (loc + 1) fps
  return (OrT_ (locBS loc, b, h) nm ps', loc')
deliteral sftn loc b h (OrF' fs [f] p) = do
  nm <- cast $ HM.lookup (False, Or fs) sftn 
  (p', loc') <- deliteral' sftn (loc + 1) False f p 
  k <- cast $ elemIndex f fs
  return (OrF_ (locBS loc, b, h) nm k p', loc')
deliteral sftn loc b h (OrF' fs gs p) = error $ show $ "single residue : " <> ppForm (Or gs)
deliteral sftn loc b h (AndT' fs [f] p) = do
  nm <- cast $ HM.lookup (True, And fs) sftn 
  (p', loc') <- deliteral' sftn (loc + 1) True f p 
  k <- cast $ elemIndex f fs
  return (AndT_ (locBS loc, b, h) nm k p', loc')
deliteral sftn loc b h (AndT' fs gs p) = error $ show $ "single residue : " <> ppForm (And gs)
deliteral sftn loc b h (AndF' fps) = do
  let (fs, _) = unzip fps
  nm <- cast $ HM.lookup  (False, And fs) sftn 
  (loc', ps') <- mapAccumM (\ loc_ (f_, p_) -> swap <$> deliteral' sftn loc_ False f_ p_) (loc + 1) fps
  return (AndF_ (locBS loc, b, h) nm ps', loc')
deliteral sftn loc b h (ImpT' f g p q) = do
  nm <- cast $ HM.lookup (True, Imp f g) sftn 
  (p', loc') <- deliteral' sftn (loc + 1) False f p 
  (q', loc'') <- deliteral' sftn loc' True g q 
  return (ImpT_ (locBS loc, b, h) nm p' q', loc'')
deliteral sftn loc b h (ImpFA' f g p) = do
  nm <- cast $ HM.lookup  (False, Imp f g) sftn 
  (p', loc') <- deliteral' sftn (loc + 1) True f p 
  return (ImpFA_ (locBS loc, b, h) nm p', loc')
deliteral sftn loc b h (ImpFC' f g p) = do
  nm <- cast $ HM.lookup (False, Imp f g) sftn 
  (p', loc') <- deliteral' sftn (loc + 1) False g p 
  return (ImpFC_ (locBS loc, b, h) nm p', loc')
deliteral sftn loc b h (IffF' f g p q) = do
  nm <- cast $ HM.lookup (False, Iff f g) sftn 
  (p', loc') <- deliteral' sftn (loc + 1) False (Imp f g) p 
  (q', loc'') <- deliteral' sftn loc' False (Imp g f) q 
  return (IffF_ (locBS loc, b, h) nm p' q', loc'')
deliteral sftn loc b h (IffTO' f g p) = do
  nm <- cast $ HM.lookup (True, Iff f g) sftn 
  (p', loc') <- deliteral' sftn (loc + 1) True (Imp f g) p 
  return (IffTO_ (locBS loc, b, h) nm p' , loc')
deliteral sftn loc b h (IffTR' f g p) = do
  nm <- cast $ HM.lookup (True, Iff f g) sftn 
  (p', loc') <- deliteral' sftn (loc + 1) True (Imp g f) p 
  return (IffTR_ (locBS loc, b, h) nm p' , loc')
deliteral sftn loc b h (FaT' vxs f p) = do
  let (vs, xs) = unzip vxs 
  nm <- cast $ HM.lookup (True, Fa vs f) sftn 
  let f' = substForm vxs f
  (p', loc') <- deliteral' sftn (loc + 1) True f' p 
  return (FaT_ (locBS loc, b, h) nm xs p', loc')
deliteral sftn loc b h (FaF' vs ms f p) = do
  nm <- cast $ HM.lookup (False, Fa vs f) sftn 
  f' <- substitute vs (L.map par ms) f
  (p', loc') <- deliteral' sftn (loc + 1) False f' p 
  return (FaF_ (locBS loc, b, h) nm ms p', loc')
deliteral sftn loc b h (ExT' vs ms f p) = do
  nm <- cast $ HM.lookup (True, Ex vs f) sftn 
  f' <- substitute vs (L.map par ms) f
  (p', loc') <- deliteral' sftn (loc + 1) True f' p 
  return (ExT_ (locBS loc, b, h) nm ms p', loc')
deliteral sftn loc b h (ExF' vxs f p) = do
  let (vs, xs) = unzip vxs 
  nm <- cast $ HM.lookup (False, Ex vs f) sftn 
  let f' = substForm vxs f
  (p', loc') <- deliteral' sftn (loc + 1) False f' p 
  return (ExF_ (locBS loc, b, h) nm xs p', loc')
deliteral sftn loc b h (Cut' f p q) = do
  (p', loc') <- deliteral' sftn (loc + 1) False f p 
  (q', loc'') <- deliteral' sftn loc' True f q 
  return (Cut_ (locBS loc, b, h) f p' q', loc'')
deliteral sftn loc b h (RelD' f p) = do
  (p', loc') <- deliteral' sftn (loc + 1) True f p 
  return (RelD_ (locBS loc, b, h) f p', loc')
deliteral sftn loc b h (AoC' x f p) = do
  (p', loc') <- deliteral' sftn (loc + 1) True f p 
  return (AoC_ (locBS loc, b, h) x f p', loc')
deliteral sftn loc b h (Mrk s p) = deliteral sftn loc b h p

checkStelabs :: Set Form -> [Stelab] -> IO ()
checkStelabs sf [] = return ()
checkStelabs sf (slb : slbs) = do 
  g <- checkStelab sf slb 
  let sf' = S.insert g sf 
  checkStelabs sf' slbs

fst4 :: (a, b, c, d) -> a
fst4 (x, _, _, _) = x

freshElabIndex :: BS -> Int
freshElabIndex ('e' :> bs) = 
  case bs2int bs of 
    Just k -> k + 1 
    _ -> 0
freshElabIndex _ = 0

elab :: Bool -> Prob -> Invranch -> [Step] -> IO Proof  -- [Elab]
elab vb tptp ivch stps = do
  slbs <- stepsToStelabs vb tptp stps
  -- checkStelabs (S.map snd $ HM.keysSet ivch) slbs
  let slbs' = L.map (removeMultiStep . desingle) slbs
  -- -- checkStelabs sf slbs'
  slbs'' <- indexStelabs 0 HM.empty slbs'
  -- -- checkStelabs sf slbs''
  -- prf <- stitch ivch ("root", True, Top) slbs''
  let frs = maximum $ L.map freshElabIndex $ HM.keys tptp ++ L.map fst4 stps
  prf <- stitch slbs''
  fst <$> deliteral' ivch frs True Top prf
  -- return $ Open_ ("root", True, Top)
  
