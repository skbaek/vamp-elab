{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module Prove where

import Types
import Basic
import Norm
import Lem
import PP
import Check (verify)

import Data.Text.Lazy.Builder (Builder)

import Data.List as L (length, null, map, find, foldl, any, filter, concatMap, concat, all, (\\))
import Data.Text.Lazy as T (Text, unpack)
import Data.Set as S
  ( Set, empty, isSubsetOf, toList, union, intersection, (\\), null, size,
    fromList, member, delete, difference, disjoint, insert, singleton, elemAt )
import Data.Map as HM
  ( Map, toList, fromList, empty, lookup, insert, isSubmapOf, map, filterWithKey, findWithDefault, mapWithKey,
    alter, foldrWithKey, notMember )
import Control.Monad as M (guard, foldM, mzero)
import Data.Maybe as MB (mapMaybe, isJust, fromMaybe)
import Control.Applicative ( Alternative((<|>)) )
import qualified Data.Bifunctor as DBF
import Data.Tuple (swap)
import System.Timeout (timeout)
import Debug.Trace (trace)
import Data.Time.Clock 

andRs :: [(Form, Prf)] -> Form -> IO Prf
andRs fps (And fs) = AndF' <$> mapM (\ f_ -> (f_,) <$> andRs fps f_) fs
andRs fps f = cast $ snd <$> L.find ((f ==) . fst) fps

orLs :: [(Form, Prf)] -> Form -> IO Prf
orLs fps (Or fs) = OrT' <$> mapM (\ f_ -> (f_,) <$> orLs fps f_) fs
orLs fps f = cast $ snd <$> L.find ((f ==) . fst) fps

orRs :: Form -> Prf -> Prf
orRs (Or fs) p = OrF' fs fs $ L.foldl (flip orRs) p fs
orRs _ p = p

andLs :: Form -> Prf -> Prf
andLs (And fs) p = AndT' fs fs $ L.foldl (flip andLs) p fs
andLs _ p = p

orIffFlatOr :: [Form] -> [Form] -> IO Prf
orIffFlatOr fs gs = do
  guardMsg "flatten result mismatch" $ flatOr fs == gs
  let gps = L.map (\ g_ -> (g_, Id' g_)) gs
  p <- orLs gps (Or fs)
  return $ iffRFull (Or fs) (Or gs) (OrF' gs gs p) (orRs (Or fs) $ OrT' gps)

andIffFlatAnd :: [Form] -> [Form] -> IO Prf
andIffFlatAnd fs gs = do
  guardMsg "flatten result mismatch" $ flatAnd fs == gs
  let gps = L.map (\ g_ -> (g_, Id' g_)) gs
  p <- andRs gps (And fs)
  return $ iffRFull (And fs) (And gs) (andLs (And fs) $ AndF' gps) (AndT' gs gs p) --(OrF' gs gs p0) (orRs (Or fs) $ OrT' gps)

pdne :: Int -> Form -> Form -> IO Prf
pdne k f g 
  | f == g = return $ iffRefl f
  | otherwise = 
    case (f, g) of
     (Not f, Not g) -> do
       p <- pdne k f g
       return $ Cut' (f <=> g) p $ iffToNotIffNot f g
     (Not (Not f), g) -> do
       p <- pdne k f g -- p : |- f <=> g
       return $ cuts [(Not (Not f) <=> f, notNotIff f), (f <=> g, p)] $ iffTrans (Not (Not f)) f g
     (Or fs, Or gs) -> do
       fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> pdne k f_ g_) fs gs
       cuts fgps <$> cast (iffsToOrIffOr fs gs)
     (And fs, And gs) -> do
       fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> pdne k f_ g_) fs gs
       cuts fgps <$> cast (iffsToAndIffAnd fs gs)
     (Imp e f, Imp g h) -> do
       pl <- pdne k e g -- pl : |- fl <=> gl 
       pr <- pdne k f h -- pl : |- fr <=> gr
       return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ impCong e f g h
     (Iff e f, Iff g h) -> do
       pl <- pdne k e g -- pl : |- fl <=> gl 
       pr <- pdne k f h -- pl : |- fr <=> gr
       return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ iffCong e f g h
     (Fa vs f, Fa ws g) -> do
       guard (vs == ws)
       let (k', vxs) = varPars k vs
       let f' = substForm vxs f
       let g' = substForm vxs g
       p <- pdne k' f' g'
       return $ Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) p) $ faIffToFaIffFa vs k f g
     (Ex vs f, Ex ws g) -> do
       guard (vs == ws)
       let (k', vxs) = varPars k vs
       let f' = substForm vxs f
       let g' = substForm vxs g
       p <- pdne k' f' g'
       return $ Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) p) $ faIffToExIffEx vs k f g
     _ -> et "prove-DNE"

prn :: Int -> Form -> Form -> IO Prf
prn k (Not f) (Not g) = do
  p <- prn k f g
  return $ Cut' (f <=> g) p $ iffToNotIffNot f g
prn k (Or fs) (Or gs) = do
  fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> prn k f_ g_) fs gs
  cuts fgps <$> cast (iffsToOrIffOr fs gs)
prn k (And fs) (And gs) = do
  fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> prn k f_ g_) fs gs
  cuts fgps <$> cast (iffsToAndIffAnd fs gs)
prn k (Imp e f) (Imp g h) = do
  pl <- prn k e g -- pl : |- fl <=> gl 
  pr <- prn k f h -- pl : |- fr <=> gr
  return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ impCong e f g h
prn k (Iff e f) (Iff g h) = do
  pl <- prn k e g -- pl : |- fl <=> gl 
  pr <- prn k f h -- pl : |- fr <=> gr
  return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ iffCong e f g h
prn k (Fa vs f) (Fa ws g) = do
  let (k', xs) = listPars k ws
  vxs <- zipM vs xs
  wxs <- zipM ws xs
  vws <- mapM2 (\ v_ w_ -> return (v_, Var w_)) vs ws
  let f' = substForm vxs f
  let f'' = substForm vws f
  let g' = substForm wxs g
  guard (substForm wxs f'' == f') 
  p <- prn k' f' g'
  Cut' (Fa ws $ f'' <=> g) (FaF' ws k (f'' <=> g) p) <$> faIffToFaIffFa'' k vs f ws g
prn k (Ex vs f) (Ex ws g) = do
  let (k', xs) = listPars k ws
  vxs <- zipM vs xs
  wxs <- zipM ws xs
  vws <- mapM2 (\ v_ w_ -> return (v_, Var w_)) vs ws
  let f' = substForm vxs f
  let f'' = substForm vws f
  let g' = substForm wxs g
  guard (substForm wxs f'' == f') 
  p <- prn k' f' g'
  Cut' (Fa ws $ f'' <=> g) (FaF' ws k (f'' <=> g) p) <$> faIffToExIffEx'' k vs f ws g
prn _ f g
  | f == g = return $ iffRefl f
  | otherwise = et "prove-rename"

vmToVxs :: VM -> [Text] -> Maybe [(Text, Term)]
vmToVxs vm = mapM (\ v_ -> (v_,) <$> HM.lookup v_ vm)

specs :: VM -> [(Term, Term)] -> Maybe VM
specs vm [] = return vm
specs vm ((x, y) : xys) = do
  vm' <- spec vm x y
  specs vm' xys

spec :: VM -> Term -> Term -> Maybe VM
spec vm (Var v) y = do
  case HM.lookup v vm of
    Just x -> do
      guard $ x == y
      return vm
    _ -> return $ HM.insert v y vm
spec vm x@(Fun f xs) y@(Fun g ys) = do
  guard $ f == g
  xys <- zipM xs ys
  foldM (\ vm_ (x_, y_) -> spec vm_ x_ y_) vm xys
spec vm x y = do
  guard (x == y)
  return vm

properMaps :: VM -> Text -> Bool
properMaps vm v = 
  case HM.lookup v vm of 
    Just x -> x /= Var v 
    _ -> False

fspec :: VM -> Form -> Form -> Maybe VM
fspec vm (Not f) (Not g) = fspec vm f g
fspec vm (Or fs) (Or gs) = foldM2 fspec vm fs gs
fspec vm (And fs) (And gs) = foldM2 fspec vm fs gs
fspec vm (Imp e f) (Imp g h) = foldM2 fspec vm [e, f] [g, h]
fspec vm (Iff e f) (Iff g h) = foldM2 fspec vm [e, f] [g, h]
fspec vm (Fa vs f) (Fa ws g) 
  | vs == ws && not (L.any (properMaps vm) vs) = do 
    vm' <- fspec vm f g 
    guard $ not (L.any (properMaps vm') vs)
    return vm'
fspec vm (Ex vs f) (Ex ws g) 
  | vs == ws && not (L.all (properMaps vm) vs) = do 
    vm' <- fspec vm f g 
    guard $ not (L.any (properMaps vm') vs)
    return vm'
fspec vm (Rel r xs) (Rel s ys) 
  | r == s = foldM2 spec vm xs ys
  | otherwise = mzero
fspec vm (Eq w x) (Eq y z) = foldM2 spec vm [w, x] [y, z]
fspec _ _ _ = mzero

putt :: Term -> Term -> Form -> IO Prf
putt x y f@(Fa vs (Eq a b)) =
  ( do vm <- cast $ specs HM.empty [(a, x), (b, y)]
       vxs <- cast $ vmToVxs vm vs
       return $ FaT' vxs (a === b) $ Id' (x === y) ) <|>
  ( do vm <- cast $ specs HM.empty [(a, y), (b, x)]
       vxs <- cast $ vmToVxs vm vs
       return $ FaT' vxs (a === b) $ EqS' y x )
putt x y (Eq a b)
  | x == a && y == b = return $ Id' (x === y)
  | x == b && y == a = return $ EqS' y x
  | otherwise = mzero

putt x y _ = et "putt : not an equation"
put :: [Form] -> Term -> Term -> IO Prf
put es x@(Fun f xs) y@(Fun g ys)
  | x == y = return $ EqR' x
  | otherwise =
    first (putt x y) es <|> do
      guard $ f == g
      xyps <- mapM2 (\ x_ y_ -> (x_ === y_,) <$> put es x_ y_) xs ys
      return $ cuts xyps $ FunC' f xs ys
put es x y
  | x == y = return $ EqR' x
  | otherwise = first (putt x y) es

puf :: Int -> [Form] -> Form -> Form -> IO Prf
puf k es (Not f) (Not g) = do
  p <- puf k es f g
  return $ Cut' (f <=> g) p $ iffToNotIffNot f g
puf k es (Or fs) (Or gs) = do
  fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> puf k es f_ g_) fs gs
  cuts fgps <$> cast (iffsToOrIffOr fs gs)
puf k es (And fs) (And gs) = do
  fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> puf k es f_ g_) fs gs
  cuts fgps <$> cast (iffsToAndIffAnd fs gs)
puf k es (Imp e f) (Imp g h) = do
  pl <- puf k es e g -- pl : |- fl <=> gl 
  pr <- puf k es f h -- pl : |- fr <=> gr
  return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ impCong e f g h
puf k es (Iff e f) (Iff g h) = do
  pl <- puf k es e g -- pl : |- fl <=> gl 
  pr <- puf k es f h -- pl : |- fr <=> gr
  return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ iffCong e f g h
puf k es (Fa vs f) (Fa ws g) = do
  guard (vs == ws)
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let g' = substForm vxs g
  p <- puf k' es f' g'
  return $ Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) p) $ faIffToFaIffFa vs k f g
puf k es (Ex vs f) (Ex ws g) = do
  guard (vs == ws)
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let g' = substForm vxs g
  p <- puf k' es f' g'
  return $ Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) p) $ faIffToExIffEx vs k f g
puf _ es (Rel r xs) (Rel s ys) = do
  xyps <- mapM2 (\ x_ y_ -> (x_ === y_,) <$> put es x_ y_) xs ys
  --  p <- relCong r xs ys
  --  return $ cuts xyps p
  cuts xyps <$> relCong r xs ys

puf _ es (Eq a b) (Eq x y) = do
  pax <- put es a x
  pby <- put es b y
  return $ 
    cuts [(a === x, pax), (b === y, pby)] $ 
      iffRFull (a === b) (x === y) 
        (Cut' (x === a) (EqS' a x) $ eqTrans2 x a b y) 
        (Cut' (y === b) (EqS' b y) $ eqTrans2 a x y b)
puf _ _ f g =
  eb $ "prove-unfold\n f : " <> ppForm f <> "\ng : " <> ppForm g <> "\n"

pfl :: Int -> Form -> Form -> IO Prf
pfl k (Not f) (Not g) = do
  p <- pfl k f g
  return $ Cut' (f <=> g) p $ iffToNotIffNot f g
pfl k (Or fs) (Or hs) = do
  let gs = L.map fltn fs
  fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> pfl k f_ g_) fs gs
  p0 <- cuts fgps <$> cast (iffsToOrIffOr fs gs)
  p1 <- orIffFlatOr gs hs
  return $ cuts [(Or fs <=> Or gs, p0), (Or gs <=> Or hs, p1)] $ iffTrans (Or fs) (Or gs) (Or hs)
pfl k (And fs) (And hs) = do
  let gs = L.map fltn fs
  fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> pfl k f_ g_) fs gs
  p0 <- cuts fgps <$> cast (iffsToAndIffAnd fs gs)
  p1 <- andIffFlatAnd gs hs
  return $ cuts [(And fs <=> And gs, p0), (And gs <=> And hs, p1)] $ iffTrans (And fs) (And gs) (And hs)
pfl k (Imp e f) (Imp g h) = do
  pl <- pfl k e g -- pl : |- fl <=> gl 
  pr <- pfl k f h -- pl : |- fr <=> gr
  return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ impCong e f g h
pfl k (Iff e f) (Iff g h) = do
  pl <- pfl k e g -- pl : |- fl <=> gl 
  pr <- pfl k f h -- pl : |- fr <=> gr
  return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ iffCong e f g h
pfl k (Fa vs f) (Fa ws g) = do
  guard (vs == ws)
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let g' = substForm vxs g
  p <- pfl k' f' g'
  return $ Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) p) $ faIffToFaIffFa vs k f g
pfl k (Ex vs f) (Ex ws g) = do
  guard (vs == ws)
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let g' = substForm vxs g
  p <- pfl k' f' g'
  return $ Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) p) $ faIffToExIffEx vs k f g
pfl _ f g
  | f == g = return $ iffRefl f
  | otherwise = et "prove-flatten"

pnm :: Int -> Form -> Form -> IO Prf
pnm k (Not f) (Not g) = do
  p <- pnm k f g
  return $ Cut' (f <=> g) p $ iffToNotIffNot f g
pnm k (Or fs) (Or gs) = do
  fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> pnm k f_ g_) fs gs
  cuts fgps <$> cast (iffsToOrIffOr fs gs)
pnm k (And fs) (And gs) = do
  fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> pnm k f_ g_) fs gs
  cuts fgps <$> cast (iffsToAndIffAnd fs gs)
pnm k (Imp e f) (Imp g h) = do
  pl <- pnm k e g -- pl : |- fl <=> gl 
  pr <- pnm k f h -- pl : |- fr <=> gr
  return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ impCong e f g h
pnm k (Iff e f) (Iff g h) = do
  pl <- pnm k e g -- pl : |- fl <=> gl 
  pr <- pnm k f h -- pl : |- fr <=> gr
  return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ iffCong e f g h
pnm k (Fa vs f) _g
  | L.any (`varInf` f) vs = do
    (ws, g) <- cast $ breakFa _g
    guardMsg "Normalized list mismatch" $ ws == L.filter (`varInf` f) vs
    let (k', wxs) = varPars k ws
    let f' = substForm wxs f
    let g' = substForm wxs g
    p <- pnm k' f' g'
    return $
      cuts
        [ (Fa vs f <=> Fa ws f, bloatFaIffFa k vs ws f),
          (Fa ws (f <=> g), FaF' ws k (f <=> g) p),
          (Fa ws f <=> Fa ws g, faIffToFaIffFa ws k f g) ] $
        iffTrans (Fa vs f) (Fa ws f) (Fa ws g)
  | otherwise = do
    -- pb $ "Variables " <> ppList ft vs <> " do not occur in " <> ppForm _g <> "\n"
    p <- pnm k f _g
    return $ cuts [(Fa vs f <=> f, bloatFaIff k vs f), (f <=> _g, p)] $ iffTrans (Fa vs f) f _g
pnm k (Ex vs f) _g
  | L.any (`varInf` f) vs = do
    (ws, g) <- cast $ breakEx _g
    guardMsg "Normalized list mismatch" $ ws == L.filter (`varInf` f) vs
    let (k', wxs) = varPars k ws
    let f' = substForm wxs f
    let g' = substForm wxs g
    p <- pnm k' f' g'
    return $
      cuts
        [ (Ex vs f <=> Ex ws f, bloatExIffEx k vs ws f),
          (Fa ws (f <=> g), FaF' ws k (f <=> g) p),
          (Ex ws f <=> Ex ws g, faIffToExIffEx ws k f g) ] $
        iffTrans (Ex vs f) (Ex ws f) (Ex ws g)
  | otherwise = do
    p <- pnm k f _g
    return $ cuts [(Ex vs f <=> f, bloatExIff k vs f), (f <=> _g, p)] $ iffTrans (Ex vs f) f _g
pnm _ f g
  | f == g = return $ iffRefl f
  | otherwise = eb $ "prove-normalized error\nf = " <> ppForm f <> "\ng = " <> ppForm g <> "\n"

useConcs :: Int -> [Form] -> IO (Int, [Form], Prf -> Prf)
useConcs k [] = return (k, [], id)
useConcs k (f : fs) = do
  (k', fs', pf) <- useConc k f
  (k'',fs'', pf') <- useConcs k' fs
  return (k'', fs' ++ fs'', pf . pf')

useConc :: Int -> Form -> IO (Int, [Form], Prf -> Prf)
useConc k (Fa vs f) = do
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  (k'', fs, pf) <- useConc k' f'
  return (k'', fs, FaF' vs k f . pf)
useConc k (Or fs) = do
  (k', fs', pp) <- useConcs k fs
  return (k', fs', OrF' fs fs . pp)
useConc k g =
  if isLit g
  then return (k, [g], id)
  else eb $ "use conc : not lit : " <> ppForm g

expandLit :: Int -> Form -> Form -> IO (Int, [Form], Prf -> Prf)
expandLit k (Not g) (Iff g' h)
  | g == g' = return (k, [Not h], \ p_ -> Cut' (Not h) p_ (notTF h g $ iffMP g h))
expandLit k g (Iff g' h)
  | g == g' = do
    (k', hs, ph) <- useConc k h
    return (k', hs, \ p_ -> Cut' h (ph p_) (iffMPR g h) )
expandLit _ _ _ = mzero

expandLits :: [Form] -> Int -> [Form] -> IO (Int, [Form], Prf -> Prf)
expandLits ds k [] = return (k, [], id)
expandLits ds k (g : gs) = do
  (k', hs, pg) <- first (expandLit k g) ds
  (k'', hs', pgs) <- expandLits ds k' gs
  return (k'', hs ++ hs', pg . pgs)

avatarSplit :: [Form] -> Form -> Form -> IO Prf
avatarSplit ds f g = do
  (k, gs, pg) <- useConc 0 g
  (_, hs, ph) <- expandLits ds k gs
  vm <- cast $ searchCnf (hs ++ gs) (HM.empty, [f])
  pf <- proveCnfTrans vm f (hs ++ gs)
  return $ pg $ ph pf

proveCnfTrans :: VM -> Form -> [Form] -> IO Prf
proveCnfTrans vm (Fa vs f) gs = do
  let vxs = L.map (\ v_ -> (v_, agvmt vm (Var v_))) vs
  let f' = substForm vxs f
  FaT' vxs f <$> proveCnfTrans vm f' gs
proveCnfTrans vm (And fs) gs =
  first (\ f_ -> AndT' fs [f_] <$> proveCnfTrans vm f_ gs) fs
proveCnfTrans vm (Or fs) gs = do
  fps <- mapM (\ f_ -> (f_,) <$> proveCnfTrans vm f_ gs) fs
  return $ OrT' fps
proveCnfTrans _ (Not (Eq x y)) gs
  | Not (Eq y x) `elem` gs = return $ notTF (x === y) (y === x) $ EqS' y x
proveCnfTrans _ (Eq x y) gs
  | Eq y x `elem` gs = return $ EqS' x y
proveCnfTrans _ f gs
  | f `elem` gs = return $ Id' f
  | otherwise = mzero

forkCnf :: VM -> [Form] -> (Form, [Form]) -> [(VM, [Form])]
forkCnf vm gls (Or fs, hs) = [(vm, fs ++ hs)]
forkCnf vm gls (Fa _ f, hs) = [(vm, f : hs)]
forkCnf vm gls (And fs, hs) = L.map (\ f_ -> (vm, f_ : hs)) fs
forkCnf vm gs (f, hs) = L.map (, hs) $ L.concatMap (ul vm f) gs

searchCnf :: [Form] -> (VM, [Form]) -> Maybe VM
searchCnf gls z = fst <$> search (L.null . snd) (\ (vm_, fs_) -> L.map (forkCnf vm_ gls) (plucks fs_)) z

search :: (Eq a, Show a) => (a -> Bool) -> (a -> [[a]]) -> a -> Maybe a
search tm br x =
  if tm x
  then return x
  else do let zss = br x
          -- guard $ [] `notElem` zss
          zs <- cast $ getShortList zss
          first (search tm br) zs

utrws :: VM -> Term -> Term -> [(Term, Term)] -> Maybe VM
utrws vm x y [] = return vm
utrws vm x y ((a, b) : abs) = do
  vm' <- utrw vm x y a b
  utrws vm' x y abs

lookUpTerm :: VM -> Term -> Maybe Term
lookUpTerm vm (Var v) = HM.lookup v vm
lookUpTerm vm _ = nt

utrw :: VM -> Term -> Term -> Term -> Term -> Maybe VM
utrw vm x y a@(Fun f xs) b@(Fun g ys) =
  ut vm a b <|>
  ( do vm' <- ut vm x a
       ut vm' y b ) <|>
  ( do xys <- zipM xs ys
       foldM (\ vm_ (a_, b_) -> utrw vm_ x y a_ b_) vm xys )
utrw vm x y a b =
  ut vm a b <|>
  ( do vm' <- ut vm x a
       ut vm' y b )

ubv :: VM -> Text -> Term -> Maybe VM
-- scheme  : ubv vm v x
-- assumes : v is unbound in vm
-- assumes : if x is a variable, it is also unbound in vm
ubv vm v x =
  let x' = avmt vm x in
  let vm' = HM.map (substVar v x') vm in
  do guard $ not $ hasVar v x'
     return $ HM.insert v x' vm'

ut :: VM -> Term -> Term -> Maybe VM
-- ut vm (Par k) (Par m) = guard (k == m) >> return vm
ut vm (Fun f xs) (Fun g ys) = do
  guard $ f == g
  xys <- zipM xs ys
  foldM (\ vm_ (x_, y_) -> ut vm_ x_ y_) vm xys
ut vm x y =
  if x == y
  then return vm
  else
    case (lookUpTerm vm x, lookUpTerm vm y, x, y) of
       (Just x', _, _, _) -> ut vm x' y
       (_, Just y', _, _) -> ut vm x y'
       (_, _, Var v, _) -> ubv vm v y
       (_, _, _, Var w) -> ubv vm w x
       (_, _, _, _) -> nt

uts :: VM -> [(Term, Term)] -> Maybe VM
uts vm [] = return vm
uts vm ((x, y) : xys) = do
  vm' <- ut vm x y
  uts vm' xys

ul :: VM -> Form -> Form -> [VM]
ul vm (Not f) (Not g) = ua vm f g
ul vm f g = ua vm f g

ua :: VM -> Form -> Form -> [VM]
ua vm (Eq s t) (Eq u v) =
  case (uts vm [(s, u), (t, v)], uts vm [(s, v), (t, u)]) of
    (Just vm', Just vm'') ->
      case (HM.isSubmapOf vm' vm'', HM.isSubmapOf vm'' vm') of
        (True, _) -> [vm']
        (_, True) -> [vm'']
        _ -> [vm', vm'']
    (Just vm', _) -> [vm']
    (_, Just vm') -> [vm']
    _ -> []
ua vm (Rel r xs) (Rel s ys) =
  if r == s
  then cast $ zipM xs ys >>= uts vm
  else []
ua vm _ _ = []

gndVar :: VM -> Text -> VM
gndVar vm v =
  case HM.lookup v vm of
    Just _ -> vm
    _ -> HM.insert v zt vm

premLits :: Form -> Maybe [Form]
premLits (Fa vs f) = premLits f
premLits (Or fs) = L.concat <$> mapM premLits fs
premLits f = guard (isLit f) >> return [f]

usePrem :: (Form -> IO Prf) -> VM -> Form -> IO Prf
usePrem  pf vm (Fa vs f) = do
  let vxs = L.map (\ v_ -> (v_, agvmt vm (Var v_))) vs
  let f' = substForm vxs f
  FaT' vxs f <$> usePrem pf vm f'
usePrem pf vm (Or fs) = do
  fps <- mapM (\ f_ -> (f_ ,) <$> usePrem pf vm f_) fs
  return $ OrT' fps
usePrem  pf _ f = pf f

mapPremLit :: [Form] -> Form -> IO Prf
mapPremLit hs f@(Not (Rel _ _)) = guard (f `elem` hs) >> return (Id' f)
mapPremLit hs f@(Rel _ _) = guard (f `elem` hs) >> return (Id' f)
mapPremLit hs (Eq x y)
  | Eq x y `elem` hs = return $ Id' (Eq x y)
  | Eq y x `elem` hs = return $ EqS' x y
  | otherwise = error "use-prem : eq"
mapPremLit hs f@(Not (Eq x y))
  | f `elem` hs = return $ Id' f
  | x == y = return $ NotT' (x === x) $ EqR' x
  | Not (Eq y x) `elem` hs = return $ NotT' (x === y) $ NotF' (y === x) $ EqS' y x
  | otherwise = eb $ "use-prem-neq : " <> ppForm f
mapPremLit _ f = eb $ "map-prem-lit-exception : " <> ppForm f <> "\n"

efactor :: Maybe Bool -> Form -> Form -> IO Prf
efactor mb f g = do
  fls <- cast $ premLits f
  (_, gls, pp) <- useConc 0 g
  avs <- claVars f
  _vm <- efctr gls (HM.empty, mb, fls)
  let vm = L.foldl gndVar (HM.map gndTerm  _vm) avs
  pf <- usePrem (mapPremLit gls) vm f
  return $ pp pf

efctr :: [Form] -> EFS -> IO VM
efctr _ (vm, _, []) = return vm
efctr gs (vm, mb, fs) = do
  let fcss = L.map (genEFSs vm mb gs) (plucks fs)
  fcs <- cast $ getShortList fcss
  first (efctr gs) fcs

genPvtAux :: VM -> Form -> Form -> [(VM, Form, Dir)]
genPvtAux vm (Not _) (Not _) = []
genPvtAux vm f (Not g) = L.map (, f, Obv) $ ua vm f g
genPvtAux vm (Not f) g = L.map (, f, Rev) $ ua vm f g
genPvtAux _ _ _ = []

genPvt :: VM -> (Form, [Form]) -> (Form, [Form]) -> [Form] -> [RSTA]
genPvt vm (f, fs) (g, gs) hs =
  L.map (\ (vm_, pvt_, dr_) -> (vm_, Just (pvt_, dr_), fs, gs, hs)) $ genPvtAux vm f g

genEF :: VM -> Maybe Bool -> Form -> [Form] -> [EFS]
genEF vm mb (Not (Eq x y)) fs =
  case ut vm x y of
    Just vm' -> [(vm', if MB.isJust mb then Just True else nt, fs)]
    _ -> []
genEF _ _ _ _ = []

genFcs :: VM -> [Form] -> (Form, [Form]) -> [FSTA]
genFcs vm gs (f, fs) = L.map (, fs) (L.concatMap (ul vm f) gs)

genEFSs :: VM -> Maybe Bool -> [Form] -> (Form, [Form]) -> [EFS]
genEFSs vm (Just True) gs (f, fs) = L.map (, Just True, fs) (L.concatMap (ul vm f) gs)
genEFSs vm mb gs (f, fs) =
  genEF vm mb f fs ++ L.map (, mb, fs) (L.concatMap (ul vm f) gs)

genLftRss :: VM -> Maybe (Form, Dir) -> [Form] -> [Form] -> (Form, [Form]) -> [RSTA]
genLftRss vm Nothing gs hs (f, fs) =
  L.concatMap (\ (g_, gs_) -> genPvt vm (f, fs) (g_, gs_) hs) (plucks gs) ++ L.map (, nt, fs, gs, hs) (L.concatMap (ul vm f) hs)
genLftRss vm pd@(Just (pvt, Obv)) gs hs (f, fs) = L.map (, pd, fs, gs, hs) $ L.concatMap (ul vm f) (pvt : hs)
genLftRss vm pd@(Just (pvt, Rev)) gs hs (f, fs) = L.map (, pd, fs, gs, hs) $ L.concatMap (ul vm f) (Not pvt : hs)

genRgtRss :: VM -> Maybe (Form, Dir) -> [Form] -> [Form] -> (Form, [Form]) -> [RSTA]
genRgtRss vm Nothing fs hs (g, gs) =
  L.concatMap (\ (f_, fs_) -> genPvt vm (f_, fs_) (g, gs) hs) (plucks fs) ++ L.map (, nt, fs, gs, hs) (L.concatMap (ul vm g) hs)
genRgtRss vm pd@(Just (pvt, Obv)) fs hs (g, gs) = L.map (, pd, fs, gs, hs) $ L.concatMap (ul vm g) (Not pvt : hs)
genRgtRss vm pd@(Just (pvt, Rev)) fs hs (g, gs) = L.map (, pd, fs, gs, hs) $ L.concatMap (ul vm g) (pvt : hs)

cnfTrans :: Form -> Form -> IO Prf
cnfTrans f g = do
  -- pt "CNF-Trans :\n"
  -- pt $ "f : " <> ppForm f <> "\n"
  -- pt $ "g : " <> ppForm g <> "\n"
  (_, gs, pp) <- useConc 0 g
  -- pt $ "gs : " <> ppList ppForm gs <> "\n"
  vm <- cast $ searchCnf gs (HM.empty, [f])
  -- pt $ "vm :\n" <> ppVM vm <> "\n"
  pf <- proveCnfTrans vm f gs
  return $ pp pf

fContained :: [Form] -> (Term, Term, Dir, SST) -> Bool
fContained hs (_, y, _, _) =
  let hfs = fsfuns hs in
  let yfs = tfuns y in
  S.isSubsetOf yfs hfs


genSST :: Dir -> [Form] -> [Form] -> (Form, [Form]) -> [(Term, Term, Dir, SST)]
genSST dr hs gs (Eq x y, fs) =
  let fs' = L.filter (\ l_ -> not (litOccursIn l_ hs)) fs in
  let gs' = L.filter (\ l_ -> not (litOccursIn l_ hs)) gs in
  [(x, y, dr, (HM.empty, fs', gs', [])), (y, x, dr, (HM.empty, fs', gs', []))]
genSST dr hs gs _ = []

genZs :: Dir -> [Form] -> [Form] -> [Form] -> [(Term, Term, Dir, SST)]
genZs dr fs gs hs =
  case unspecs fs hs of
    (_ : _ : _) -> []
    [ffs] -> L.filter (fContained hs) $ genSST dr hs gs ffs
    [] -> L.concatMap (genSST dr hs gs) (plucks fs)

lspec :: Form -> Form -> Bool
lspec (Not f) (Not g) = aspec f g
lspec f g = aspec f g



aspec :: Form -> Form -> Bool
aspec (Rel r xs) (Rel s ys) = r == s && MB.isJust (zipM xs ys >>= specs HM.empty)
aspec (Eq x y) (Eq a b) = MB.isJust $ specs HM.empty [(x, a), (y, b)] <|> specs HM.empty [(x, b), (y, a)]
aspec _ _ = False

unspecs :: [Form] -> [Form] -> [(Form, [Form])]
unspecs fls hls = L.filter (\ (f_, _) -> not (L.any (lspec f_) hls)) (plucks fls)

cutIff :: Form -> Form -> Prf -> Prf -> Prf
cutIff f g pfg p = Cut' (f <=> g) pfg $ Cut' g (iffMP f g) p


nubIndexForm :: Form -> Int
nubIndexForm (Not f) = nubIndexForm f
nubIndexForm (Or fs) = maximum $ 0 : L.map nubIndexForm fs
nubIndexForm (And fs) = maximum $ 0 : L.map nubIndexForm fs
nubIndexForm (Imp f g) = maximum $ L.map nubIndexForm [f, g]
nubIndexForm (Iff f g) = maximum $ L.map nubIndexForm [f, g]
nubIndexForm (Fa vs f) = maximum $ nubIndexForm f : L.map nubIndexVar vs
nubIndexForm (Ex vs f) = maximum $ nubIndexForm f : L.map nubIndexVar vs
nubIndexForm _ = 0

nubIndexVar :: Text -> Int
nubIndexVar ('X' :> t) = 
  case readInt t of  
    Just k -> k + 1
    _ -> 0
nubIndexVar _ = 0

nubForms :: [Form] -> [Form]
nubForms fs = do
  let k = maximum (L.map nubIndexForm fs) 
  fst $ rnfs HM.empty k fs

resolve :: Form -> Form -> Form -> IO Prf
resolve f g h = do
  let [f', g'] = nubForms [f, g]
  fls <- cast $ premLits f'
  gls <- cast $ premLits g'
  -- (_, hls) <- cast $ concLits 0 h
  (_, hls, ph) <- useConc 0 h
  (_vm, _p, dr) <- rslv (HM.empty, nt, fls, gls, hls)
  fvs <- claVars f'
  gvs <- claVars g'
  let avs = S.toList (S.union fvs gvs)
  let vm = L.foldl gndVar (HM.map gndTerm  _vm) avs
  let pvt =  subf vm _p
  prff' <- prn 0 f f'
  prfg' <- prn 0 g g'
  -- pb $ "DR : " <> ppDir dr <> "\n"
  case dr of
    Obv -> do
      pf <- usePrem (mapPremLit (pvt : hls)) vm f'
      pg <- usePrem (mapPremLit (Not pvt : hls)) vm g'
      return $ cutIff f f' prff' $ cutIff g g' prfg' $ ph $ Cut' pvt pf $ Cut' (Not pvt) pg (NotT' pvt $ Id' pvt)
    Rev -> do
      pf <- usePrem (mapPremLit (Not pvt : hls)) vm f'
      pg <- usePrem (mapPremLit (pvt : hls)) vm g'
      return $ cutIff f f' prff' $ cutIff g g' prfg' $ ph $ Cut' pvt pg $ Cut' (Not pvt) pf (NotT' pvt $ Id' pvt)

eqfInit :: (Form, [Form]) -> [(Term, Term, [Form])]
eqfInit (Not (Eq x y), fs) = [(x, y, fs), (y, x, fs)]
eqfInit _ = []

eqfactor :: Form -> Form -> IO Prf
eqfactor f g = do
  fs <- cast $ premLits f
  -- (_, ggs) <- cast $ concLits 0 g
  (_, ggs, pg) <- useConc 0 g
  let xygs = L.concatMap eqfInit $ plucks ggs
  (vm, x, y, gs) <- first (\ (x_, y_, gs_) -> eqf x_ y_ gs_ (HM.empty, fs, [])) xygs

  pf <- usePrem (\f_ -> first (rwf x y f_) gs) vm f
  let eqpf
        | Not (x === y) `elem` ggs = NotF' (x === y) pf
        | Not (y === x) `elem` ggs = NotF' (y === x) $ Cut' (x === y) (EqS' y x) pf
        | otherwise = error "eqf : nonexistent eqn"
  return $ pg eqpf

superpose :: Form -> Form -> Form -> IO Prf
superpose f g h = do
  -- pt $ "f : " <> ppForm f <> "\n"
  -- pt $ "g : " <> ppForm g <> "\n"
  -- pt $ "h : " <> ppForm h <> "\n"
  let [f', g'] = nubForms [f, g]
  -- pt $ "f' : " <> ppForm f' <> "\n"
  -- pt $ "g' : " <> ppForm g' <> "\n"
  fls <- cast $ premLits f'
  gls <- cast $ premLits g'
  (_, hls, ph) <- useConc 0 h
  -- pt $ "f-lits :\n" <> ppListNl ppForm fls <> "\n"
  -- pt $ "g-lits :\n" <> ppListNl ppForm gls <> "\n"
  -- pt $ "h-lits :\n" <> ppListNl ppForm hls <> "\n"
  let zos = genZs Obv fls gls hls
  let zrs = genZs Rev gls fls hls
  let zs = zos ++ zrs
  (x, y, dr, vm) <- first (\ (x_, y_, dr_, z_) -> super x_ y_ dr_ hls z_) zs
  prff' <- prn 0 f f'
  prfg' <- prn 0 g g'
  pfg <- case dr of
           Obv -> suprf vm x y f' g' hls
           Rev -> suprf vm x y g' f' hls
  return $ cutIff f f' prff' $ cutIff g g' prfg' $ ph pfg

rwt :: Term -> Term -> Term -> Term -> IO Prf
rwt x y a@(Fun f xs) b@(Fun g ys)
  | a == b = return $ EqR' a
  | x == a && y == b = return $ Id' (x === y)
  | otherwise = do
    guard $ f == g
    xyps <- mapM2 (\ x_ y_ -> (x_ === y_,) <$> rwt x y x_ y_) xs ys
    return $ cuts xyps $ FunC' f xs ys
rwt x y a b
  | a == b = return $ EqR' a
  | x == a && y == b = return $ Id' (x === y)
  | otherwise = mzero
rwf :: Term -> Term -> Form -> Form -> IO Prf
rwf x y (Not f) (Not g) = do
   p <- rwf y x g f
   return $ Cut' (y === x) (EqS' x y) $ notTF f g p
rwf x y (Rel r xs) (Rel s ys) = do
  guard $ r == s
  xyps <- mapM2 (\ x_ y_ -> (x_ === y_,) <$> rwt x y x_ y_) xs ys
  return $ cuts xyps $ RelC' r xs ys
rwf x y (Eq a b) (Eq c d) =
  ( do pac <- rwt x y a c
       pbd <- rwt x y b d
       return $ cuts [(a === c, pac), (b === d, pbd), (c === a, EqS' a c)] $ eqTrans2 c a b d) <|>
  ( do pad <- rwt x y a d
       pbc <- rwt x y b c
       return $ cuts [(a === d, pad), (b === c, pbc), (b === a, EqS' a b), (c === b, EqS' b c)] $ eqTrans2 c b a d)
rwf _ _ _ _ = mzero

useEqPremLit :: Term -> Term -> Prf -> Form -> [Form] -> IO Prf
useEqPremLit x y p f@(Eq a b) hs
  | (x == a) && (y == b) = return p
  | (x == b) && (y == a) = return $ Cut' (x === y) (EqS' a b) p
  | otherwise = mapPremLit hs f
useEqPremLit x y p f hs = mapPremLit hs f

suprf :: VM -> Term -> Term -> Form -> Form -> [Form] -> IO Prf
suprf vm x y f g hs = do
  -- pt "VM =\n"
  -- pt $ ppVM vm
  -- pt $ "x = " <> ppTerm x <> "\n"
  -- pt $ "y = " <> ppTerm y <> "\n"
  -- pt $ "g = " <> ppForm g <> "\n"
  -- pt $ "hs =\n" <> ppListNl ppForm hs <> "\n"
  pp <- usePrem (\g_ -> first (rwf x y g_) hs) vm g
  usePrem (flip (useEqPremLit x y pp) hs) vm f

subt :: VM -> Term -> Term
subt vm (Var v) =
  case HM.lookup v vm of
    Just x -> x
    _ -> Var v
subt vm (Fun f xs) = Fun f $ L.map (subt vm) xs

subf ::  VM -> Form -> Form
subf vm (Eq x y) =
  let x' = subt vm x in
  let y' = subt vm y in
  Eq x' y'
subf vm (Rel r xs) = Rel r $ L.map (subt vm) xs
subf vm (Not f) = Not $ subf vm f
subf vm (Imp f g) =
  let f' = subf vm f in
  let g' = subf vm g in
  Imp f' g'
subf vm (Iff f g) =
  let f' = subf vm f in
  let g' = subf vm g in
  Iff f' g'
subf vm (Or fs)  = Or  $ L.map (subf vm) fs
subf vm (And fs) = And $ L.map (subf vm) fs
subf vm (Fa vs f) =
  let vm' = HM.filterWithKey (\ v_ _ -> v_ `notElem` vs) vm in
  Fa vs $ subf vm' f
subf vm (Ex vs f) =
  let vm' = HM.filterWithKey (\ v_ _ -> v_ `notElem` vs) vm in
  Ex vs $ subf vm' f

tryGndLit :: VM -> Form -> Maybe Form
tryGndLit vm f = do
  f' <- tavmf vm f
  guard $ isGndLit f'
  return f'

superatv :: VM -> [Form] -> [Form] -> [(Term, Term)] -> (Form, [Form]) -> [SST]
superatv vm hs gs xys (f, fs) =
  case tryGndLit vm f of
    Just f' ->
      [(vm, fs, gs, xys) | litOccursIn f' hs]
    _ -> L.map (, fs, gs, xys) $ L.concatMap (ul vm f) hs

superpsv :: VM -> Term -> Term -> [Form] -> [Form] -> [(Term, Term)] -> (Form, [Form]) -> [SST]
superpsv vm x y hs fs xys (g, gs) = L.map (\ xys_ ->(vm, fs, gs, xys_ ++ xys)) $ L.concatMap (genRWEqs g) hs

supereq :: VM -> Term -> Term -> [Form] -> [Form] -> [Form] -> ((Term, Term), [(Term, Term)]) -> [SST]
supereq vm x y hs fs gs ((Fun f xs, Fun g ys), xys) =
  let lft = case ut vm (Fun f xs) (Fun g ys) of
              Just vm' -> [(vm', fs, gs, xys)]
              _ -> [] in
  let mid = case uts vm [(x, Fun f xs), (y, Fun g ys)] of
              Just vm' -> [(vm', fs, gs, xys)]
              _ -> [] in
  let rgt = case (f == g, zipM xs ys) of
              (True, Just abs) -> [(vm, fs, gs, abs ++ xys)]
              _ -> [] in
  lft ++ mid ++ rgt
supereq vm x y hs fs gs ((a, b), xys) =
  let lft = case ut vm a b of
              Just vm' -> [(vm', fs, gs, xys)]
              _ -> [] in
  let rgt = case uts vm [(x, a), (y, b)] of
              Just vm' -> [(vm', fs, gs, xys)]
              _ -> [] in
  lft ++ rgt

genRWEqs :: Form -> Form -> [[(Term, Term)]]
genRWEqs (Not g) (Not h) = genRWEqs g h
genRWEqs (Rel r xs) (Rel s ys) =
  case (r == s, zipM xs ys) of
    (True, Just xys) -> [xys]
    _ -> []
genRWEqs (Eq x y) (Eq a b) = [[(x, a), (y, b)], [(x, b), (y, a)]]
genRWEqs _ _ = []

eqfbranch :: Term -> Term -> [Form] -> EQFS -> [[EQFS]]
eqfbranch x y gs (vm, fs, xys) =
  let fbs = L.map (eqfLit vm gs xys) (plucks fs) in
  let ebs = L.map (eqfEq vm x y fs) (plucks xys) in
  fbs ++ ebs

eqfLit :: VM -> [Form] -> [(Term, Term)] -> (Form, [Form]) -> [EQFS]
eqfLit vm gs xys (f, fs) = L.map (\ xys_ ->(vm, fs, xys_ ++ xys)) $ L.concatMap (genRWEqs f) gs

eqfEq :: VM -> Term -> Term -> [Form] -> ((Term, Term), [(Term, Term)]) -> [EQFS]
eqfEq vm x y fs ((Fun f xs, Fun g ys), xys) =
  let lft = case ut vm (Fun f xs) (Fun g ys) of
              Just vm' -> [(vm', fs, xys)]
              _ -> [] in
  let mid = case uts vm [(x, Fun f xs), (y, Fun g ys)] of
              Just vm' -> [(vm', fs, xys)]
              _ -> [] in
  let rgt = case (f == g, zipM xs ys) of
              (True, Just abs) -> [(vm, fs, abs ++ xys)]
              _ -> [] in
  lft ++ mid ++ rgt
eqfEq vm x y fs ((a, b), xys) =
  let lft = case ut vm a b of
              Just vm' -> [(vm', fs, xys)]
              _ -> [] in
  let rgt = case uts vm [(x, a), (y, b)] of
              Just vm' -> [(vm', fs, xys)]
              _ -> [] in
  lft ++ rgt

superbranch :: Term -> Term -> [Form] -> SST -> [[SST]]
superbranch x y hs (vm, fs, gs, xys) =
  let abs = L.map (superatv vm hs gs xys) (plucks fs) in
  let pbs = L.map (superpsv vm x y hs fs xys) (plucks gs) in
  let ebs = L.map (supereq vm x y hs fs gs) (plucks xys) in
  abs ++ pbs ++ ebs

genRss :: RSTA -> [[RSTA]]
genRss (vm, pd, fs, gs, hs) =
  let lft = L.map (genLftRss vm pd gs hs) (plucks fs) in
  let rgt = L.map (genRgtRss vm pd fs hs) (plucks gs) in
  lft ++ rgt

fctr :: [Form] -> FSTA -> IO VM
fctr _ (vm, []) = return vm
fctr gs (vm, fs) = do
  let fcss = L.map (genFcs vm gs) (plucks fs)
  fcs <- cast $ getShortList fcss
  first (fctr gs) fcs

mapSearchBranch :: VM -> [Form] -> [Form] -> [[(VM, [Form])]]
mapSearchBranch vm fs gs =
  L.map (\ (f_, fs_) -> L.concatMap (L.map (, fs_) . ul vm f_) gs) (plucks fs)

mapSearch :: VM -> [Form] -> [Form] -> IO VM
mapSearch vm [] _ = return vm
mapSearch vm fs gs = do
  let zss = mapSearchBranch vm fs gs
  zs <- cast $ getShortList zss
  first (\ (vm_, fs_) -> mapSearch vm_ fs_ gs) zs

origTimeLimit :: NominalDiffTime
origTimeLimit = 10

origSearch :: UTCTime -> Bool -> Int -> VC -> [(Form, Form)] -> IO (Maybe VC)
origSearch _ md dt vc [] = return (Just vc)
origSearch t0 md dt vc fgs = do
  t <- getCurrentTime
  let df = diffUTCTime t t0
  if df < origTimeLimit
  then let zss = L.map (origForkAux md vc) (plucks fgs) in
       do zs <- cast $ getShortList zss
          first (uncurry $ origSearch t0 md (dt + 1)) zs
  else return Nothing

super :: Term -> Term -> Dir -> [Form] -> SST -> IO (Term, Term, Dir, VM)
super x y dr hs (vm , [], [], []) = do
  let x' = agvmt vm x
  let y' = agvmt vm y
  return (x', y', dr, vm)
super x y dr hs z = do
  let zss = superbranch x y hs z
  zs <- cast $ getShortList zss
  first (super x y dr hs) zs

eqf :: Term -> Term -> [Form] -> (VM, [Form], [(Term, Term)]) -> IO (VM, Term, Term, [Form])
eqf x y gs (vm, [], []) = return (vm, x, y, gs)
eqf x y gs z = do
  let zss = eqfbranch x y gs z
  zs <- cast $ getShortList zss
  first (eqf x y gs) zs

rslv :: RSTA -> IO (VM, Form, Dir)
rslv (vm, Just (pvt, dr), [], [], _) = return (vm, pvt, dr)
rslv r = do
  let rss = genRss r
  rs <- cast $ getShortList rss
  first rslv rs

stepOrigFsGs :: Maybe [(Form, [Form], Form, [Form])] -> VC -> [Form] -> [Form] -> [Form] -> [(Form, [Form], Form, [Form])]
stepOrigFsGs Nothing   vc _ [] _ = []
stepOrigFsGs (Just tp) vc _ [] _ = tp
stepOrigFsGs mtps      vc sf (f : fs) ggs =
  case stepOrigFGs vc f ggs of
    [] -> []
    [(g, gs)] -> [(f, sf ++ fs, g, gs)]
    ggss ->
      let ntps = Just $ L.map (\ (g_, gs_) -> (f, sf ++ fs, g_, gs_)) ggss in
      case mtps of
        Nothing -> stepOrigFsGs ntps vc (f : sf) fs ggs
        Just hhss ->
          if shorter ggss hhss
          then stepOrigFsGs ntps vc (f : sf) fs ggs
          else stepOrigFsGs mtps vc (f : sf) fs ggs

-- stepOrigFGs :: VC -> Form -> [Form] -> [(Form, [Form])]
-- stepOrigFGs vc f ggs =
--   let tuples = MB.mapMaybe (\ (g_, gs_) -> (, (g_, gs_)) <$> origSearchMB vc [(f, g_)]) (plucks ggs) in
--   let results = representatives (\ (vc0, _) (vc1, _) -> vc0 == vc1) tuples in
--   L.map snd results

stepOrigFGs :: VC -> Form -> [Form] -> [(Form, [Form])]
stepOrigFGs vc f gs = L.filter (candidate vc f . fst) (plucks gs)

candidate :: VC -> Form -> Form -> Bool
candidate vc f g = 
  let vs = S.toList (formVars f) in
  let ws = S.toList (formVars g) in
  L.all (candVar vc ws) vs

candVar :: VC -> [Text] -> Text -> Bool
candVar (vw, _) ws v = 
  case HM.lookup v vw of 
    Just s -> overlaps (S.toList s) ws 
    _ -> False

overlaps :: (Eq a) => [a] -> [a] -> Bool
overlaps xs ys = L.any (`elem` ys) xs

representatives :: (a -> a -> Bool) -> [a] -> [a]
representatives _ [] = []
representatives eqc (x : xs) =
  let xs' = L.filter (not . eqc x) xs in
  x : representatives eqc xs'

origForkAux :: Bool -> VC -> ((Form, Form), [(Form, Form)]) -> [(VC, [(Form, Form)])]
origForkAux md vc (fg, fgs) = L.map (DBF.second (++ fgs)) $ origFork md vc fg

origFork :: Bool -> VC -> (Form, Form) -> [(VC, [(Form, Form)])]
origFork md vc (Rel r xs, Rel s ys)
  | r == s = do
    vc' <- cast $ conTerms vc xs ys
    return (vc', [])
origFork md vc (Eq x y, Eq a b) =
  case (conTerms vc [x, y] [a, b], conTerms vc [x, y] [b, a]) of
    (Just vc', Nothing) -> [(vc', [])]
    (Nothing, Just vc') -> [(vc', [])]
    (Just vc', Just vc'') ->
      if vc' == vc''
      then [(vc', [])]
      else [(vc', []), (vc'', [])]
    _ -> []
origFork md vc (Not f, Not g) = [(vc, [(f, g)])]
origFork md vc (Imp e f, Imp g h) = [(vc, [(e, g), (f, h)])]
origFork md vc (Iff e f, Iff g h) = [(vc, [(e, g), (f, h)])]
origFork md vc (Fa vs f, Fa ws g) = do
  vc' <- cast $ conVars vs ws vc
  return (vc', [(f, g)])
origFork md vc (Ex vs f, Ex ws g) = do
  vc' <- cast $ conVars vs ws vc
  return (vc', [(f, g)])
origFork _ vr (Or [], Or []) = [(vr, [])]
origFork _ vr (And [], And []) = [(vr, [])]
origFork _ vc (Or [f], Or [g]) = [(vc, [(f, g)])]
origFork _ vc (And [f], And [g]) = [(vc, [(f, g)])]
origFork True vc (Or fs, Or gs) 
  | L.length fs == L.length gs =
    L.map (\ (f_, fs_, g_, gs_) -> (vc, [(f_, g_), (Or fs_, Or gs_)])) $ stepOrigFsGs nt vc [] fs gs
origFork True vc (And fs, And gs) 
  | L.length fs == L.length gs =
    L.map (\ (f_, fs_, g_, gs_) -> (vc, [(f_, g_), (And fs_, And gs_)])) $ stepOrigFsGs nt vc [] fs gs
origFork False vc (Or fs, Or gs) 
  | L.length fs == L.length gs =
    let l = [(f_, fs_, g_, gs_) | (f_, fs_) <- plucks fs, (g_, gs_) <- plucks gs] in
    L.map (\ (f_, fs_, g_, gs_) -> (vc, [(f_, g_), (Or fs_, Or gs_)])) l
origFork False vc (And fs, And gs) 
  | L.length fs == L.length gs =
    let l = [(f_, fs_, g_, gs_) | (f_, fs_) <- plucks fs, (g_, gs_) <- plucks gs] in
    L.map (\ (f_, fs_, g_, gs_) -> (vc, [(f_, g_), (And fs_, And gs_)])) l
origFork md vc _ = []

pickPair :: (Text, Set Text) -> Maybe (Text, Text)
pickPair (v, ws) = do 
  guard $ 1 < S.size ws 
  return (v, S.elemAt 0 ws)

unconstPair :: VC -> Maybe (Text, Text)
unconstPair (vw, _) = first pickPair $ HM.toList vw

pruneVC :: VC -> VC
pruneVC vc = 
  case unconstPair vc of 
    Just (x, y) -> 
      case conVar x y vc of 
        Just vc' -> pruneVC vc' 
        _ -> error "cannot constrain with pair"
    _ -> vc



vcToVrAux :: HM.Map Text (Set Text) -> HM.Map Text Text
vcToVrAux vws = do
  let vwss = HM.toList vws
  HM.fromList $ MB.mapMaybe (\ (v_, ws_) -> (v_,) <$> breakSingleton (S.toList ws_)) vwss

vcToVr :: VC -> VR
vcToVr (vws, wvs) = (vcToVrAux vws, vcToVrAux wvs)

rectify :: Form -> Form -> IO Prf
rectify f g = do
  let nf = delVacVars f
  p0 <- pnm 0 f nf
  p1 <- orig nf g
  return $ cutIff f nf p0 p1

rnt :: MTT -> Term -> Term
rnt mp (Var v) = 
  case HM.lookup v mp of
    Just w -> Var w
    _ -> et "unbound variable detected\n"
rnt mp (Fun f xs) = Fun f $ L.map (rnt mp) xs

rnfs :: MTT -> Int -> [Form] -> ([Form], Int)
rnfs mp k [] = ([], k)
rnfs mp k (f : fs) = 
  let (f', k') = rnf mp k f in
  DBF.first (f' :) $ rnfs mp k' fs 

rnf :: MTT -> Int -> Form -> (Form, Int)
rnf mp k (Rel r xs) = (Rel r (L.map (rnt mp) xs), k)
rnf mp k (Eq x y) = (Eq (rnt mp x) (rnt mp y), k)
rnf tt ti (Not f) = DBF.first Not $ rnf tt ti f
rnf tt ti (Or fs) = DBF.first Or $ rnfs tt ti fs
rnf tt ti (And fs) = DBF.first And $ rnfs tt ti fs
rnf mp k (Imp f g) = 
  let (f', k') = rnf mp k f in
  let (g', k'') = rnf mp k' g in
  (Imp f' g', k'')
rnf mp k (Iff f g) = 
  let (f', k') = rnf mp k f in
  let (g', k'') = rnf mp k' g in
  (Iff f' g', k'')
rnf tt ti (Fa vs f) = 
  let (vs', tt', ti') = rnvs tt ti vs in
  let (f', ti'') = rnf tt' ti' f in
  (Fa vs' f', ti'')
rnf tt ti (Ex vs f) = 
  let (vs', tt', ti') = rnvs tt ti vs in
  let (f', ti'') = rnf tt' ti' f in
  (Ex vs' f', ti'')

rnvs :: MTT -> Int -> [Text] -> ([Text], MTT, Int)
rnvs mp k [] = ([], mp, k)
rnvs mp k (v : vs) =
  let v' = "X" <> tlt (ppInt k) in
  let mp' = HM.insert v v' mp in
  let (vs', mp'', k') = rnvs mp' (k + 1) vs in
  (v' : vs', mp'', k')

conAux :: Text -> Set Text -> VC -> Maybe VC
conAux v nws (vws, wvs) = do
  ws <- HM.lookup v vws
  let wsi = S.intersection ws nws
  let wso = ws S.\\ nws
  guard $ not $ S.null wsi
  let vws' = HM.insert v wsi vws
  let wvs' = HM.mapWithKey (conAuxAux v wso) wvs
  return (vws', wvs')

conVars :: [Text] -> [Text] -> VC -> Maybe VC
conVars vs ws vc = do
  (vws, wvs) <- foldM (\ vc_ v_ -> conAux v_ (S.fromList ws) vc_) vc vs
  (wvs', vws') <- foldM (\ vc_ w_ -> conAux w_ (S.fromList vs) vc_) (wvs, vws) ws
  return (vws', wvs')

conVar :: Text -> Text -> VC -> Maybe VC
conVar v w = conVars [v] [w]
conTerms :: VC -> [Term] -> [Term] -> Maybe VC
conTerms vm [] [] = return vm
conTerms vm (x : xs) (y : ys) = do
  vm' <- conTerm vm x y
  conTerms vm' xs ys
conTerms _ _ _ = nt

conTerm :: VC -> Term -> Term -> Maybe VC
conTerm vc (Var v) (Var w) =
  case conVar v w vc of
    Just vc' -> Just vc'
    _ -> mzero
conTerm vm (Fun f xs) (Fun g ys) = do
  guard (f == g) -- "Cannot ground function"
  conTerms vm xs ys
conTerm vm x y = do
  guard (x == y) -- "Cannot ground pair\n" <> ppTerm x <> "\n" <> ppTerm y <> "\n"
  return vm

orig :: Form -> Form -> IO Prf
orig f g 
  | f == g = return $ Id' f
  | otherwise = do
    (f', g', pf) <- origPrep f g
    cvc <- makeVC f' g'
    t0 <- getCurrentTime
    mvc <- origSearch t0 True 0 cvc [(f', g')]
    case mvc of 
      Just vc -> 
        do let vr = vcToVr $ pruneVC vc
           p <- porg' vr 0 f' g' <|> error "porg-failure"
           verify 0 S.empty (S.singleton (f' <=> g')) p 
           return $ Cut' (f <=> g) (pf p) $ iffMP f g
      _ -> pt "Orig timeout!\n" >> return Open'

-- failAsm :: Int -> IO Prf -> IO Prf
-- failAsm k pf = do
--   rst <- timeout k (pf <|> return Open')
--   case rst of 
--     Just p -> return p 
--     _ -> return Open' 

constraint :: Set Text -> Set Text -> Map Text (Set Text)
constraint vs ws = L.foldl (\ m_ v_ -> HM.insert v_ ws m_) HM.empty (S.toList vs)

makeVC :: Form -> Form -> IO VC
makeVC f g = do
  let vs = formVars f
  let ws = formVars g
  return (constraint vs ws, constraint ws vs)

-- makeVC :: Form -> Form -> IO VC
-- makeVC f g = do
--   let vs = formVars f
--   let ws = formVars g
--   let fsgs = formSigs HM.empty [] f
--   let gsgs = formSigs HM.empty [] g
--   let fm = groupByTextKey fsgs
--   let gm = groupByTextKey gsgs
--   pb $ "f : " <> ppForm f <> "\n"
--   pb $ "g : " <> ppForm g <> "\n"
--   let vswss = mergeBySigs fm gm
--   -- pt $ ppListNl (\ (vs_, ws_) -> ppList id vs_ <> " <-|-> " <> ppList id ws_) vswss 
--   -- et "todo"
--   foldM (\ vc_ (vs_, ws_) -> cast (conVars vs_ ws_ vc_)) (initVC vs ws) vswss

formSigs :: Sigs -> [PrePath] -> Form -> Sigs
formSigs sg pts (Eq x y) = do
  let sg' = termSigs sg (PreEq : pts) x
  termSigs sg' (PreEq : pts) y
formSigs sg pts (Rel r xs) =
  let ptxs = extendPrePathsRel pts r 0 xs in
  L.foldl (uncurry . termSigs) sg ptxs
formSigs sg pts (Not f) =  formSigs sg (PreNot : pts) f
formSigs sg pts (Imp f g) =
  let sg' = formSigs sg (PreImpL : pts) f in
  formSigs sg' (PreImpR : pts) g
formSigs sg pts (Iff f g) =
  let sg' = formSigs sg (PreIffL : pts) f in
  formSigs sg' (PreIffR : pts) g
formSigs sg pts (Fa vs f) =
  let sg' = L.foldl varSigs sg vs in
  formSigs sg' (PreFa vs : pts) f
formSigs sg pts (Ex vs f) =
  let sg' = L.foldl varSigs sg vs in
  formSigs sg' (PreEx vs : pts) f
formSigs sg pts (Or fs)  = L.foldl (\ sg_ (f_, fs_) -> formSigs sg_ (PreOr  (posCount fs_) (negCount fs_) : pts) f_) sg (plucks fs)
formSigs sg pts (And fs) = L.foldl (\ sg_ (f_, fs_) -> formSigs sg_ (PreAnd (posCount fs_) (negCount fs_) : pts) f_) sg (plucks fs)

markNonOcc :: PrePath -> Path
markNonOcc (PreFa _) = NewFa False
markNonOcc (PreEx _) = NewEx False
markNonOcc (PreRel r k) = NewRel r k
markNonOcc (PreFun f k) = NewFun f k
markNonOcc (PreOr k m) = NewOr k m
markNonOcc (PreAnd k m) = NewAnd k m
markNonOcc PreImpL = NewImpL
markNonOcc PreImpR = NewImpR
markNonOcc PreIffL = NewIffL
markNonOcc PreIffR = NewIffR
markNonOcc PreEq = NewEq
markNonOcc PreNot = NewNot

markFstOcc :: Text -> [PrePath] -> [Path]
markFstOcc _ [] = et "unbound var"
markFstOcc v (PreFa vs : pts) =
  if v `elem` vs
  then NewFa True  : L.map markNonOcc pts
  else NewFa False : markFstOcc v pts
markFstOcc v (PreEx vs : pts) =
  if v `elem` vs
  then NewEx True  : L.map markNonOcc pts
  else NewEx False : markFstOcc v pts
markFstOcc v (pt : pts) =
  markNonOcc pt : markFstOcc v pts

termSigs :: Sigs -> [PrePath] -> Term -> Sigs
termSigs sg pts (Var v) =
  let npts = markFstOcc v pts in
  case HM.lookup v sg of
    Just mp ->
      let mp' = HM.alter succMaybe npts mp in
      HM.insert v mp' sg
    _ -> et $ "Signature does not include var : " <> v
termSigs sg pts (Fun f xs) =
  let ptxs = extendPrePathsFun pts f 0 xs in
  L.foldl (uncurry . termSigs) sg ptxs
--termSigs sg _ (Par _) = sg

insertBySig :: Text -> Maybe [Text] -> Maybe [Text]
insertBySig v (Just vs) = Just (v : vs)
insertBySig v _ = Just [v]

groupByTextKey :: (Ord a) => HM.Map Text a -> HM.Map a [Text]
groupByTextKey = HM.foldrWithKey (HM.alter . insertBySig) HM.empty

succMaybe :: Maybe Int -> Maybe Int
succMaybe (Just k) = Just (k + 1)
succMaybe _ = Just 1

mergeBySigs :: Map Sig [Text] -> Map Sig [Text] -> [([Text], [Text])]
mergeBySigs fm gm =
  HM.foldrWithKey
    (\ sg_ vs_ ->
      case HM.lookup sg_ gm of
        Just ws ->
          if L.length vs_ == L.length ws
          then ((vs_, ws) :)
          else et "Cannot merge sigs : 0"
        _ -> eb ("Signature present in only one map,\nVS : " <> ppList ft vs_ <> "\nSig : " <> ppSig sg_ <> "\nOther Sigs :\n" <> ppHM ppSig (ppList ft) gm) )
    [] fm

uniqVars :: [Form] -> Bool
uniqVars fs = isJust $ foldM uniqVarsCore S.empty fs

uniqVarsAux :: Set Text -> Text -> Maybe (Set Text)
uniqVarsAux vs v 
  | S.member v vs = nt
  | otherwise = return $ S.insert v vs

uniqVarsCore :: Set Text -> Form -> Maybe (Set Text)
uniqVarsCore vs (Not f) = uniqVarsCore vs f
uniqVarsCore vs (Or fs) = foldM uniqVarsCore vs fs
uniqVarsCore vs (And fs) = foldM uniqVarsCore vs fs
uniqVarsCore vs (Imp f g) = foldM uniqVarsCore vs [f, g] 
uniqVarsCore vs (Iff f g) = foldM uniqVarsCore vs [f, g] 
uniqVarsCore vs (Fa ws f) = foldM uniqVarsAux vs ws >>= (`uniqVarsCore` f)
uniqVarsCore vs (Ex ws f) = foldM uniqVarsAux vs ws >>= (`uniqVarsCore` f)
uniqVarsCore vs _ = return vs

rnPrep :: Form -> Form -> IO (Form, Form, Prf -> Prf)
rnPrep f g 
  | uniqVars [f, g] = return (f, g, id)
  | otherwise = do
    let [f', g'] = nubForms [f, g]
    pf <- prn 0 f f' -- pfrn : |- f <=> f'
    pg <- prn 0 g' g -- pfrn : |- f <=> f'
    return (f', g', \ p_ -> iffsTrans [(f, pf), (f', p_), (g', pg)] g)

-- dneConcPrep :: Form -> Form -> IO (Form, Prf -> Prf)
-- dneConcPrep f (Not (Not g)) = 
--   return (g, \ p_ -> iffsTrans [(f, p_), (g, iffNotNot g)] (Not (Not g)))
-- dneConcPrep f g = return (g, id)

dnePrep :: Form -> Form -> IO (Form, Form, Prf -> Prf)
dnePrep f (Not (Not g)) 
  | dne f == f = 
    return (f, g, \ p_ -> iffsTrans [(f, p_), (g, iffNotNot g)] (Not (Not g)))
  | otherwise = do
    let f' = dne f 
    p <- pdne 0 f f'
    return (f', g, \ p_ -> iffsTrans [(f, p), (f', p_), (g, iffNotNot g)] (Not (Not g)))
dnePrep f g
  | dne f == f = return (f, g, id)
  | otherwise = do 
    let f' = dne f 
    p <- pdne 0 f f'
    return (f', g, \ p_ -> iffsTrans [(f, p), (f', p_)] g)

flatPrep :: Form -> Form -> IO (Form, Form, Prf -> Prf)
flatPrep f g 
  | fltn f == f && fltn g == g = return (f, g, id)
  | fltn f /= f && fltn g == g = do
    let f' = fltn f 
    p <- pfl 0 f f'
    return (f', g, \ p_ -> iffsTrans [(f, p), (f', p_)] g)
  | fltn f == f && fltn g /= g = do
    let g' = fltn g 
    p <- pfl 0 g g'
    return (f, g', \ p_ -> iffsTrans [(f, p_), (g', Cut' (g <=> g') p (iffSym g g'))] g)
  | otherwise = do 
    let f' = fltn f 
    let g' = fltn g 
    pf <- pfl 0 f f'
    pg <- pfl 0 g g'
    return (f', g', \ p_ -> iffsTrans [(f, pf), (f', p_), (g', Cut' (g <=> g') pg (iffSym g g'))] g)

origPrep :: Form -> Form -> IO (Form, Form, Prf -> Prf)
origPrep f g = do
  (f0, g0, pf0) <- rnPrep f g  
  (f1, g1, pf1) <- dnePrep f0 g0
  (f2, g2, pf2) <- flatPrep f1 g1
  -- (g'', pf3) <- dneConcPrep f''' g'
  return (f2, g2, pf0 . pf1 . pf2)

conAuxAux :: Text -> Set Text -> Text -> Set Text -> Set Text
conAuxAux v wso w vs =
  if S.member w wso
  then S.delete v vs
  else vs

varSigs :: Sigs -> Text -> Sigs
varSigs sg v =
  case HM.lookup v sg of
    Just _ -> et "var-new-sigs"
    _ -> HM.insert v HM.empty sg

extendPrePathsRel :: [PrePath] -> Funct -> Int -> [Term] -> [([PrePath], Term)]
extendPrePathsRel pts r k [] = []
extendPrePathsRel pts r k (x : xs) = (PreRel r k : pts, x) : extendPrePathsRel pts r (k + 1) xs

extendPrePathsFun :: [PrePath] -> Funct -> Int -> [Term] -> [([PrePath], Term)]
extendPrePathsFun pts f k [] = []
extendPrePathsFun pts f k (x : xs) = (PreFun f k : pts, x) : extendPrePathsFun pts f (k + 1) xs

posCount :: [Form] -> Int
posCount fs = L.length $ L.filter isPos fs

negCount :: [Form] -> Int
negCount fs = L.length $ L.filter isNeg fs

porig :: Int -> Form -> Form -> IO Prf
porig k f g 
  | f == g = return $ iffRefl f
  | otherwise = do
    case (f, g) of
     (Eq x y, Eq y' x') -> do 
       guard $ x == x' && y == y'
       return $ iffRFull (x === y) (y === x) (EqS' x y) (EqS' y x)
     (Not f, Not g) -> do
       p <- porig k f g
       return $ Cut' (f <=> g) p $ iffToNotIffNot f g
     (Or fs, Or gs) -> do
       fgps <- porigAux k fs gs
       let fgs = L.map (\ (f_, g_, _) -> (f_, g_)) fgps
       let iffps = L.map (\ (f_, g_, p_) -> (f_ <=> g_, p_)) fgps
       cuts iffps <$> cast (iffsToOrIffOr' fgs fs gs)
     (And fs, And gs) -> do
       fgps <- porigAux k fs gs
       let fgs = L.map (\ (f_, g_, _) -> (f_, g_)) fgps
       let iffps = L.map (\ (f_, g_, p_) -> (f_ <=> g_, p_)) fgps
       cuts iffps <$> cast (iffsToAndIffAnd' fgs fs gs)
     (Imp e f, Imp g h) -> do
       pl <- porig k e g -- pl : |- fl <=> gl 
       pr <- porig k f h -- pl : |- fr <=> gr
       return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ impCong e f g h
     (Iff e f, Iff g h) -> do
       pl <- porig k e g -- pl : |- fl <=> gl 
       pr <- porig k f h -- pl : |- fr <=> gr
       return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ iffCong e f g h
     (Fa vs f, Fa ws g) -> do
       let (k', xs) = listPars k ws
       wxs <- zipM ws xs
       vws <- zipM vs $ L.map Var ws
       let g' = substForm wxs g
       let f' = substForm vws f
       let f'' = substForm wxs f'
       p <- porig k' f'' g'
       Cut' (Fa ws $ f' <=> g) (FaF' ws k (f' <=> g) p) <$> faIffToFaIffFa'' k vs f ws g
     (Ex vs f, Ex ws g) -> do
       let (k', xs) = listPars k ws
       wxs <- zipM ws xs
       vws <- zipM vs $ L.map Var ws
       let g' = substForm wxs g
       let f' = substForm vws f
       let f'' = substForm wxs f'
       p <- porig k' f'' g'
       Cut' (Fa ws $ f' <=> g) (FaF' ws k (f' <=> g) p) <$> faIffToExIffEx'' k vs f ws g
     (f, g) -> mzero 

porg' :: VR -> Int -> Form -> Form -> IO Prf
porg' vr k f g = do
  porg vr k f g 

porg :: VR -> Int -> Form -> Form -> IO Prf
porg vm k f g 
  | f == g = return $ iffRefl f
  | otherwise = do
    case (f, g) of
     (Eq x y, Eq y' x') -> do 
       guard $ x == x' && y == y'
       return $ iffRFull (x === y) (y === x) (EqS' x y) (EqS' y x)
     (Not f, Not g) -> do
       p <- porg' vm k f g
       return $ Cut' (f <=> g) p $ iffToNotIffNot f g
     (Or fs, Or gs) -> do
       fgps <- porgAux vm k fs gs
       let fgs = L.map (\ (f_, g_, _) -> (f_, g_)) fgps
       let iffps = L.map (\ (f_, g_, p_) -> (f_ <=> g_, p_)) fgps
       cuts iffps <$> cast (iffsToOrIffOr' fgs fs gs)
     (And fs, And gs) -> do
       fgps <- porgAux vm k fs gs
       let fgs = L.map (\ (f_, g_, _) -> (f_, g_)) fgps
       let iffps = L.map (\ (f_, g_, p_) -> (f_ <=> g_, p_)) fgps
       cuts iffps <$> cast (iffsToAndIffAnd' fgs fs gs)
     (Imp e f, Imp g h) -> do
       pl <- porg' vm k e g -- pl : |- fl <=> gl 
       pr <- porg' vm k f h -- pl : |- fr <=> gr
       return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ impCong e f g h
     (Iff e f, Iff g h) -> do
       pl <- porg' vm k e g -- pl : |- fl <=> gl 
       pr <- porg' vm k f h -- pl : |- fr <=> gr
       return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ iffCong e f g h
     (Fa vs f, Fa ws g) -> do
       let (k', xs) = listPars k ws
       wxs <- zipM ws xs
       vws <- mapM (pairWithVR' vm) vs 
       let g' = substForm wxs g
       let fp = substForm vws f
       let fp' = substForm wxs fp
       p <- porg' vm k' fp' g'
       Cut' (Fa ws $ fp <=> g) (FaF' ws k (fp <=> g) p) <$> genFaIffToFaIffFa vm k vs f ws g
     (Ex vs f, Ex ws g) -> do
       let (k', xs) = listPars k ws
       wxs <- zipM ws xs
       vws <- mapM (pairWithVR' vm) vs 
       let g' = substForm wxs g
       let fp = appVrForm vm f
       let fp = substForm vws f
       let fp' = substForm wxs fp
       p <- porg' vm k' fp' g'
       Cut' (Fa ws $ fp <=> g) (FaF' ws k (fp <=> g) p) <$> genFaIffToExIffEx (Fa ws $ fp <=> g) vm k vs f ws g
     (f, g) -> mzero 

uvm :: Int -> VR -> Form -> Form -> IO Prf
uvm k vr f g =
  if f == g
  then return $ Id' f
  else uvmr k vr f g

uvmr :: Int -> VR -> Form -> Form -> IO Prf
uvmr k vm (Or fs) (Or gs) = do
  let fs' = flatOr fs
  let gs' = flatOr gs
  fps <- useOrVR k vm fs' gs'
  -- orLs fps (Or fs) >>= orRs (Or gs)
  orRs (Or gs) <$> orLs fps (Or fs)

uvmr k vm (And fs) (And gs) = do
  let fs' = flatAnd fs
  let gs' = flatAnd gs
  gps <- useAndVR k vm fs' gs'
  -- andRs gps (And gs) >>= andLs (And fs)
  andLs (And fs) <$> andRs gps (And gs)

uvmr _ _ f@(Rel _ _) g@(Rel _ _) = do
  guard (f == g)
  return $ Id' f

uvmr _ _ f@(Eq x y) (Eq z w)
  | x == z && y == w = return $ Id' f
  | x == w && y == z = return $ EqS' x y
  | otherwise = mzero

uvmr k vm (Not f) (Not g) = do
  p <- uvm k (swap vm) g f
  return $ notTF f g p
uvmr k vm (Not (Not f)) g = do
  p <- uvm k vm f g
  return $ NotT' (Not f) $ NotF' f p
uvmr k vm f (Not (Not g)) = do
  p <- uvm k vm f g
  return $ NotF' (Not g) $ NotT' g p

uvmr k vm (Imp fl fr) (Imp gl gr) = do
  pl <- uvm k (swap vm) gl fl
  pr <- uvm k vm fr gr
  return $ ImpT' fl fr (ImpFA' gl gr pl) (ImpFC' gl gr pr)

uvmr k vm f@(Iff fl fr) g@(Iff gl gr) = do
  pol <- uvm k (swap vm) gl fl -- pol : gl |- fl
  por <- uvm k vm fr gr         -- por : fr |- gr
  prr <- uvm k (swap vm) gr fr -- prr : gr |- fr
  prl <- uvm k vm fl gl         -- prl : fl |- gl
  let po = IffTO' fl fr $ ImpT' fl fr pol por -- po : gl |- gr
  let pr = IffTR' fl fr $ ImpT' fr fl prr prl -- pr : gr |- gl
  return $ IffF' gl gr (impFAC gl gr po) (impFAC gr gl pr)

uvmr k vm (Fa vs f) (Fa ws g) = do
  let (k', xs) = listPars k ws
  wxs <- zipM ws xs
  let ys = L.map (pairWithVR vm wxs) vs
  vys <- zipM vs ys
  let f' = substForm vys f
  let g' = substForm wxs g
  p <- uvm k' vm f' g'
  return $ FaF' ws k g $ FaT' vys f p

uvmr k vm (Ex vs f) (Ex ws g) = do
  let (k', xs) = listPars k vs
  vxs <- zipM vs xs
  let ys = L.map (pairWithVR (swap vm) vxs) ws
  wys <- zipM ws ys
  let f' = substForm vxs f
  let g' = substForm wys g
  p <- uvm k' vm f' g'
  return $ ExT' vs k f $ ExF' wys g p

uvmr _ _ f g = mzero -- error $ unpack $ "use-VR umimplemented :\n" <> "f = " <> ppForm f <> "\ng = " <> ppForm g <> "\n"

useOrVR :: Int -> VR -> [Form] -> [Form] -> IO  [(Form, Prf)]
useOrVR _ _ [] [] = return []
useOrVR k vm (f : fs) ggs = do
  (p, gs) <- first (\ (g_, gs_) -> (, gs_) <$> uvm k vm f g_) $ plucks ggs
  fps <- useOrVR k vm fs gs
  return $ (f, p) : fps
useOrVR _ _ [] (_ : _) = mzero

useAndVR :: Int -> VR -> [Form] -> [Form] -> IO  [(Form, Prf)]
useAndVR _ _ [] [] = return []
useAndVR k vm ffs (g : gs) = do
  (p, fs) <- first (\ (f_, fs_) -> (, fs_) <$> uvm k vm f_ g) $ plucks ffs
  gps <- useAndVR k vm fs gs
  return $ (g, p) : gps
useAndVR _ _ (_ : _) [] = mzero

addVM :: Text -> Term -> VM -> Maybe VM
addVM v x gm =
  case HM.lookup v gm of
    Just y ->
      if x == y
      then return gm
      else nt
    _ -> return $ HM.insert v x gm

initVC :: Set Text -> Set Text -> VC
initVC vs ws =
  let lvs = S.toList vs in
  let lws = S.toList ws in
  let vws = HM.fromList (L.map (, ws) lvs) in
  let wvs = HM.fromList (L.map (, vs) lws) in
  (vws, wvs)

emptyVR :: VR
emptyVR = (HM.empty, HM.empty)

df1rw :: [Form] -> Form -> IO (Form, Form)
df1rw [] _ = mzero
df1rw (Fa vs (Iff l r) : es) g =
  if g == l
  then return (Fa vs (l <=> r), r)
  else df1rw es g
df1rw (Iff l r : es) g =
  if g == l
  then return (l <=> r, r)
  else df1rw es g
df1rw (e : es) f = eb $ "non-definition : " <> ppForm e

dfj :: [Form] -> [Form] -> IO (Form, [Form])
dfj es (f : fs) = (DBF.second (: fs) <$> df1 es f) <|> (DBF.second (f :) <$> dfj es fs)
dfj _ [] = mzero


df1 :: [Form] -> Form -> IO (Form, Form)
df1 es (Ex vs f) = DBF.second (Ex vs) <$> df1 es f
df1 es (Fa vs f) = DBF.second (Fa vs) <$> df1 es f
df1 es (And fs)  = DBF.second And <$> dfj es fs
df1 es (Or fs)   = DBF.second Or <$> dfj es fs
df1 es (Not f)   = DBF.second Not <$> df1 es f
df1 es (Imp f g) = (DBF.second (`Imp` g) <$> df1 es f) <|> (DBF.second (Imp f) <$> df1 es g)
df1 es (Iff f g) = (DBF.second (`Iff` g) <$> df1 es f) <|> (DBF.second (Iff f) <$> df1 es g)
df1 _ (Eq _ _) = mzero
df1 es g@(Rel _ _) = df1rw es g

dff :: [Form] -> Form -> Form -> IO [(Form, Form)]
dff es f g =
  if f == g
  then return []
  else do (e, g') <- df1 es g
          ((e, g') :) <$> dff es f g'

duts :: [(Dir, Form)] -> [Term] -> Maybe [Term]
duts es (x : xs) = ((: xs) <$> dut es x) <|> ((x :) <$> duts es xs)
duts es [] = mzero

dut :: [(Dir, Form)] -> Term -> Maybe Term
dut es x@(Fun f xs) = (Fun f <$> duts es xs) <|> first (dutt x) es
dut es x = first (dutt x) es

dutt :: Term -> (Dir, Form) -> Maybe Term
dutt x (Obv, Fa vs (Eq a b)) = do
  vm <- cast $ spec HM.empty a x
  return $ subt vm b
dutt x (Rev, Fa vs (Eq a b)) = do
  vm <- cast $ spec HM.empty b x
  return $ subt vm a
dutt x (Obv, Eq a b)
  | x == a = return b
  | otherwise = nt
dutt x (Rev, Eq a b)
  | x == b = return a
  | otherwise = nt
dutt _ (dr, f) = eb $ "non-equation : " <> ppForm f <> "\n"

du :: [(Dir, Form)] -> Term -> Term -> IO USOL
du es x y = do
  if x == y
  then return []
  else do x' <- cast $ dut es x
          (x' :) <$> du es x' y

dufAux :: [(Dir, Form)] -> Form -> (Form, [Form]) -> IO ([Form], (Form, [USOL]))
dufAux es g (f, fs) = (fs,) <$> duf es f g

dufs :: [(Dir, Form)] -> [Form] -> [Form] -> IO ([Form], [(Form, [USOL])])
dufs es = mapAccumM (\ fs_ g_ -> first (dufAux es g_) (plucks fs_))

duf :: [(Dir, Form)] -> Form -> Form -> IO (Form, [USOL])
duf es (Not f)   (Not g)   = DBF.first Not <$> duf es f g
duf es (Ex vs f) (Ex ws g) = DBF.first (Ex vs) <$> duf es f g
duf es (Fa vs f) (Fa ws g) = DBF.first (Fa vs) <$> duf es f g
duf es (And fs)  (And gs)  = do
  (fs', xss) <- unzip . snd <$> dufs es fs gs
  return (And fs', L.concat xss)
duf es (Or fs)   (Or gs)   = do
  (fs', xss) <- unzip . snd <$> dufs es fs gs
  return (Or fs', L.concat xss)
duf es (Imp e f) (Imp g h) = do
  (e', xsl) <- duf es e g
  (f', xsr) <- duf es f h
  return (Imp e' f', xsl ++ xsr)
duf es (Iff e f) (Iff g h) = do
  (e', xsl) <- duf es e g
  (f', xsr) <- duf es f h
  return (Iff e' f', xsl ++ xsr)
duf es (Eq w x)  (Eq y z)  =
  ( do ws <- du es w y
       xs <- du es x z
       return (w === x, [ws, xs]) ) <|>
  ( do xs <- du es x y
       ws <- du es w z
       return (x === w, [xs, ws]) )
duf es (Rel r xs) (Rel s ys) = (Rel r xs,) <$> mapM2 (du es) xs ys
duf _ _ _ = mzero

headFix :: Set Funct -> Term -> Bool
headFix dfs (Fun f _) = S.member f dfs
headFix dfs _ = False

obvEq :: Set Funct -> Form -> (Dir, Form)
obvEq dfs f@(Fa vs (Eq a b))
  | headFix dfs a && disjoint dfs (tfuns b) = (Obv, f)
  | headFix dfs b && disjoint dfs (tfuns a) = (Rev, f)
  | otherwise = et "obv-eq : cannot fix direction"
obvEq dfs f@(Eq a b)
  | headFix dfs a && disjoint dfs (tfuns b) = (Obv, f)
  | headFix dfs b && disjoint dfs (tfuns a) = (Rev, f)
  | otherwise = et "obv-eq : cannot fix direction"
obvEq dfs _ = et "obv-eq : non-equation"

dunfold :: [Form] -> Form -> Form -> IO Prf
dunfold es f h = do
  let dfs = ffuns f S.\\ ffuns h
  let des = L.map (obvEq dfs) es
  (f', uss) <- duf des f h
  -- pt "Unfold solution found :\n"
  -- pt $ ppListNl ppUsol uss
  (h', gs) <- dips f' uss
  guardMsg "Simultaneous substitution result does not match target" $ h == h'
  -- pt "All interpolants :\n"
  -- pt $ ppListNl ppForm gs
  -- pt $ "f : " <> ppForm f <> "\n"
  -- pt $ "f' : " <> ppForm f' <> "\n"
  pl <- ppuf 0 f f'
  pr <- uips (puf 0 es) f' gs h
  return $ Cut' f' (Cut' (f <=> f') pl (iffMP f f')) pr

porigAux :: Int -> [Form] -> [Form] -> IO [(Form, Form, Prf)]
porigAux _ [] _ = return []
porigAux k (f : fs) ggs = do
  ((g, p), gs) <- pluckFirst (\ g_ -> (g_,) <$> porig k f g_) ggs
  fgps <- porigAux k fs gs
  return ((f, g, p) : fgps)

porgAux :: VR -> Int -> [Form] -> [Form] -> IO [(Form, Form, Prf)]
porgAux _ _ [] _ = return []
porgAux vm k (f : fs) ggs = do
  ((g, p), gs) <- pluckFirst (\ g_ -> (g_,) <$> porg' vm k f g_) ggs
  fgps <- porgAux vm k fs gs
  return ((f, g, p) : fgps)

ppufAux :: Int -> [Form] -> [Form] -> IO [(Form, Form, Prf)]
ppufAux _ [] _ = return []
ppufAux k (f : fs) ggs = do
  ((g, p), gs) <- pluckFirst (\ g_ -> (g_,) <$> ppuf k f g_) ggs
  fgps <- ppufAux k fs gs
  return ((f, g, p) : fgps)

ppuf :: Int -> Form -> Form -> IO Prf
ppuf k (Not f) (Not g) = do
  p <- ppuf k f g
  return $ Cut' (f <=> g) p $ iffToNotIffNot f g
ppuf k (Or fs) (Or gs) = do
  fgps <- ppufAux k fs gs
  let fgs = L.map (\ (f_, g_, _) -> (f_, g_)) fgps
  let iffps = L.map (\ (f_, g_, p_) -> (f_ <=> g_, p_)) fgps
  cuts iffps <$> cast (iffsToOrIffOr' fgs fs gs)
ppuf k (And fs) (And gs) = do
  fgps <- ppufAux k fs gs
  let fgs = L.map (\ (f_, g_, _) -> (f_, g_)) fgps
  let iffps = L.map (\ (f_, g_, p_) -> (f_ <=> g_, p_)) fgps
  cuts iffps <$> cast (iffsToAndIffAnd' fgs fs gs)
ppuf k (Imp e f) (Imp g h) = do
  pl <- ppuf k e g -- pl : |- fl <=> gl 
  pr <- ppuf k f h -- pl : |- fr <=> gr
  return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ impCong e f g h
ppuf k (Iff e f) (Iff g h) = do
  pl <- ppuf k e g -- pl : |- fl <=> gl 
  pr <- ppuf k f h -- pl : |- fr <=> gr
  return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ iffCong e f g h
ppuf k (Fa vs f) (Fa ws g) = do
  guard (vs == ws)
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let g' = substForm vxs g
  p <- ppuf k' f' g'
  return $ Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) p) $ faIffToFaIffFa vs k f g
ppuf k (Ex vs f) (Ex ws g) = do
  guard (vs == ws)
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let g' = substForm vxs g
  p <- ppuf k' f' g'
  return $ Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) p) $ faIffToExIffEx vs k f g
ppuf _ (Rel r xs) (Rel s ys) = do
  guard $ r == s && xs == ys
  return $ iffRefl (Rel r xs)
ppuf _ (Eq x y) (Eq a b)
  | x == a && y == b = return $ iffRefl (x === y)
  | x == b && y == a = return $ iffRFull (x === y) (a === b) (EqS' x y) (EqS' a b)
  | otherwise = mzero
ppuf _ f g = mzero

sliceUsols :: [USOL] -> ([Maybe Term], [USOL])
sliceUsols [] = ([], [])
sliceUsols ([] : uss) =
  let (mxs, uss') = sliceUsols uss in
  (nt : mxs, [] : uss')
sliceUsols ((x : xs) : uss) =
  let (mxs, uss') = sliceUsols uss in
  (Just x : mxs, xs : uss')

dips :: Form -> [USOL] -> IO (Form, [Form])
dips f uss =
  if L.all L.null uss
  then return (f, [])
  else do let (mxs, uss') = sliceUsols uss
          ([], g) <- ssubf mxs f
          (h, gs) <- dips g uss'
          return (h, g : gs)

ssubts :: [Maybe Term] -> [Term] -> IO ([Maybe Term], [Term])
ssubts mxs [] = return (mxs, [])
ssubts (Just x : mxs) (_ : xs) = DBF.second (x :) <$> ssubts mxs xs
ssubts (_ : mxs) (x : xs) = DBF.second (x :) <$> ssubts mxs xs
ssubts [] (_ : _) = mzero

ssubf :: [Maybe Term] -> Form -> IO ([Maybe Term], Form)
ssubf mxs (Not f) = DBF.second Not <$> ssubf mxs f
ssubf mxs (Imp f g) = do
  (mxs', f') <- ssubf mxs f
  (mxs'', g') <- ssubf mxs' g
  return (mxs'', f' ==> g')
ssubf mxs (Iff f g) = do
  (mxs', f') <- ssubf mxs f
  (mxs'', g') <- ssubf mxs' g
  return (mxs'', f' <=> g')
ssubf mxs (Or fs) = DBF.second Or <$> mapAccumM ssubf mxs fs
ssubf mxs (And fs) = DBF.second And <$> mapAccumM ssubf mxs fs
ssubf mxs (Fa vs f) = DBF.second (Fa vs) <$> ssubf mxs f
ssubf mxs (Ex vs f) = DBF.second (Ex vs) <$> ssubf mxs f
ssubf mxs (Eq x y) = do
  (mxs', [x', y']) <- ssubts mxs [x, y]
  return (mxs', Eq x' y')
ssubf mxs (Rel r xs) = DBF.second (Rel r) <$> ssubts mxs xs

definFold :: [Form] -> Form -> Form -> IO Prf
definFold es f g = do
  -- pt $ "DFF Defins =\n" <> ppListNl ppForm es <> "\n"
  -- pt $ "DFF Source = " <> ppForm f <> "\n"
  -- pt $ "DFF Target = " <> ppForm g <> "\n"
  egs <- dff es f g
  -- pt $ ppListNl (\ (e_, g_) -> ppForm e_ <> "\n================\n" <> ppForm g_ <> "\n\n") egs
  -- pt "Begin use-GM...\n"
  uegs f egs g
  -- pt "use-GM success!\n"

uufs :: Form -> [(Form, Form)] -> Form -> IO Prf
uufs f [] h = do
  guardMsg "f and g not equal after rewriting" $ f == h
  return $ Id' f
uufs f ((e, g) : egs) h = do
  -- pt $ "f to be rewritten : " <> ppForm f <> "\n"
  -- pt $ "equation e : " <> ppForm e <> "\n"
  -- pt $ "interpolant g : " <> ppForm g <> "\n"
  pl <- uuf 0 f e g -- pgh : |- h <=> g
  pr <- uufs g egs h
  return $ Cut' g (Cut' (f <=> g) pl (IffTO' f g $ mp f g)) pr

uips :: (Form -> Form -> IO Prf) -> Form -> [Form] -> Form -> IO Prf
uips pf f [] h = do
  guardMsg "f and g not equal after rewriting" $ f == h
  return $ Id' f
uips pf f (g : gs) h = do
  pl <- pf f g
  pr <- uips pf g gs h  -- pgh : |- h <=> g
  return $ Cut' g (Cut' (f <=> g) pl (IffTO' f g $ mp f g)) pr

uegs :: Form -> [(Form, Form)] -> Form -> IO Prf
uegs f [] h = do
  guardMsg "f and g not equal after rewriting" $ f == h
  return $ Id' f
uegs f ((e, g) : egs) h = do
  pl <- uegs f egs g
  phg <- ueg 0 HM.empty h e g -- pgh : |- h <=> g
  return $ Cut' g pl $ Cut' (h <=> g) phg (IffTR' h g $ mp g h)

ueg :: Int -> VM -> Form -> Form -> Form -> IO Prf
ueg k gm f e g =
  if f == g
  then return $ iffRefl f
  else uegt gm f e g <|> uegr k gm f e g

uut :: Term -> Form -> Term -> IO Prf
uut x e y =
  if x == y
  then return $ EqR' x
  else uutt x e y <|> uutr x e y

uutr :: Term -> Form -> Term -> IO Prf
uutr (Fun f xs) e (Fun g ys) = do
  guard $ f == g
  xyps <- mapM2 (\ x_ y_ -> (x_ === y_,) <$> uut x_ e y_) xs ys
  return $ cuts xyps $ FunC' f xs ys
uutr _ _ _ = et "uutr cannot recurse"

uutt :: Term -> Form -> Term -> IO Prf
uutt x (Eq a b) y =
  case (x == a, y == b, x == b, y == a) of
    (True, True, _, _) -> return $ Id' (x === y)
    (_, _, True, True) -> return $ EqS' a b
    _ -> mzero
uutt x (Fa vs (Eq a b)) y =
  case (specs HM.empty [(a, x), (b, y)], specs HM.empty [(a, y), (b, x)] ) of
    (Just vm, _) -> do
      vxs <- mapM (\ v_ -> (v_ ,) <$> cast (HM.lookup v_ vm)) vs
      return $ FaT' vxs (a === b) $ Id' (x === y)
    (_, Just vm) -> do
      vxs <- mapM (\ v_ -> (v_ ,) <$> cast (HM.lookup v_ vm)) vs
      return $ FaT' vxs (a === b) $ EqS' y x
    _ -> mzero
uutt _ f _ = et "not an equation"

uuf :: Int -> Form -> Form -> Form -> IO Prf
uuf k (Rel r xs) e (Rel s ys) = do
  guard $ r == s
  xyps <- mapM2 (\ x_ y_ -> (x_ === y_,) <$> uut x_ e y_) xs ys
  cuts xyps <$> relCong r xs ys
uuf k (Fa vs f) e (Fa ws g) = do
  guard (vs == ws)
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let g' = substForm vxs g
  p <- uuf k' f' e g'
  return $ Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) p) $ faIffToFaIffFa vs k f g
uuf k (Not f) e (Not g) = do
  p <- uuf k f e g
  return $ Cut' (f <=> g) p $ iffToNotIffNot f g
uuf _ f _ g = eb $ "uuf unimplmented case,\nf : " <> ppForm f <> "\ng : " <> ppForm g <> "\n"

vxsToVm :: [(Text, Term)] -> VM
vxsToVm = L.foldl (\ vm_ (v_, x_) -> HM.insert v_ x_ vm_) HM.empty

uegr :: Int -> VM -> Form -> Form -> Form -> IO Prf
uegr k gm (Not f) e (Not g) = do
  p <- ueg k gm f e g
  return $ Cut' (f <=> g) p $ iffToNotIffNot f g
uegr k gm (Or fs) e (Or gs) = do
  ps <- mapM2 (\ f_ g_ -> ueg k gm f_ e g_) fs gs
  fgs <- mapM2 (\ f_ g_ -> return $ Iff f_ g_) fs gs
  fgps <- zipM fgs ps
  cuts fgps <$> cast (iffsToOrIffOr fs gs)
uegr k gm (And fs) e (And gs) = do
  ps <- mapM2 (\ f_ g_ -> ueg k gm f_ e g_) fs gs
  fgs <- mapM2 (\ f_ g_ -> return $ Iff f_ g_) fs gs
  fgps <- zipM fgs ps
  cuts fgps <$> cast (iffsToAndIffAnd fs gs)
uegr k gm (Imp fl fr) e (Imp gl gr) = do
  pl <- ueg k gm fl e gl -- pl : |- fl <=> gl 
  pr <- ueg k gm fr e gr -- pl : |- fr <=> gr
  return $ Cut' (fl <=> gl) pl $ Cut' (fr <=> gr) pr $ impCong fl fr gl gr
uegr k gm (Iff fl fr) e (Iff gl gr) = do
  pl <- ueg k gm fl e gl -- pl : |- fl <=> gl 
  pr <- ueg k gm fr e gr -- pl : |- fr <=> gr
  return $ Cut' (fl <=> gl) pl $ Cut' (fr <=> gr) pr $ iffCong fl fr gl gr
uegr k gm (Fa vs f) e (Fa ws g) = do
  guard (vs == ws)
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let g' = substForm vxs g
  gm' <- foldM (\ gm_ (v_, x_) -> cast $ addVM v_ x_ gm_) gm vxs
  p <- ueg k' gm' f' e g'
  return $ Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) p) $ faIffToFaIffFa vs k f g
uegr k gm (Ex vs f) e (Ex ws g) = do
  guard (vs == ws)
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let g' = substForm vxs g
  gm' <- foldM (\ gm_ (v_, x_) -> cast $ addVM v_ x_ gm_) gm vxs
  p <- ueg k' gm' f' e g'
  return $ Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) p) $ faIffToExIffEx vs k f g
uegr _ _ f e g =
  eb $ "UEGR failed:\n f : " <> ppForm f <> "\ne : " <> ppForm e <> "\ng : " <> ppForm g <> "\n"

uegt :: VM -> Form -> Form -> Form -> IO Prf
uegt gm f (Iff l r) g = do
  guard $ l == f
  guard $ r == g
  return $ Id' (f <=> g)
uegt gm f (Fa vs (Iff l r)) g = do
  vxs <- cast $ mapM (\ v_ -> (v_ ,) <$> HM.lookup v_ gm) vs
  let l' = substForm vxs l
  let r' = substForm vxs r
  guard $ l' == f
  guard $ r' == g
  return $ FaT' vxs (l <=> r) $ Id' (f <=> g)
uegt _ _ e _ = eb $ "Not a definition : " <> ppForm e

revDir :: Dir -> Dir
revDir Obv = Rev
revDir Rev = Obv

diffPreds :: Form -> Form -> Set Funct
diffPreds f g = S.difference (formPreds f) (formPreds g)
  
iffsTrans :: [(Form, Prf)] -> Form -> Prf
iffsTrans [] g = iffRefl g
iffsTrans [(f, p)] g = p
iffsTrans ((f, pf) : (g, pg) : l) h = 
  Cut' (f <=> g) pf $ Cut' (g <=> h) (iffsTrans ((g, pg) : l) h) $ iffTrans f g h

ppp :: Int -> Form -> Form -> IO Prf
ppp k (Or []) _ = return $ OrT' []
ppp k _ (And []) = return $ AndF' []
ppp k (Not f) (Not g) = notTF f g <$> ppp k g f
ppp k (Or fs) (Or gs) = do
  fps <- mapM2 (\ f_ g_ -> (f_,) <$> ppp k f_ g_) fs gs
  return $ OrF' gs gs $ OrT' fps
ppp k (And fs) (And gs) = do
  gps <- mapM2 (\ f_ g_ -> (g_,) <$> ppp k f_ g_) fs gs
  return $ AndT' fs fs $ AndF' gps
ppp k (Imp e f) (Imp g h) = do 
  pge <- ppp k g e 
  pfh <- ppp k f h
  return $ impFAC g h $ ImpT' e f pge pfh
ppp k (Fa vs f) (Fa ws g) = do 
  guard $ vs == ws 
  let (k', vxs) = varPars k vs 
  let f' = substForm vxs f
  let g' = substForm vxs g
  p <- ppp k' f' g'
  return $ FaF' vs k g $ FaT' vxs f  p
ppp k (Ex vs f) (Ex ws g) = do 
  guard $ vs == ws 
  let (k', vxs) = varPars k vs 
  let f' = substForm vxs f
  let g' = substForm vxs g
  p <- ppp k' f' g'
  return $ ExT' vs k f $ ExF' vxs g p
ppp k f g = guard (f == g) >> return (Id' f)

avatarComp :: Form -> Form -> IO Prf -- Ctx
avatarComp f@(Iff l r) g =
  avatarCompCore f g <|>
  ( do p <- avatarCompCore (Iff r l) g
       return $ Cut' (r <=> l) (iffSym l r) p )
avatarComp _ _ = et "avatar-comp : not iff"

avatarCompCore :: Form -> Form -> IO Prf -- Ctx
avatarCompCore (Iff s f) g = do
  (_, ggs, pp) <- useConc 0 g
  -- (_, ggs) <- cast $ concLits 0 g
  gs <- cast $ deleteOnce (Not s) ggs
  fs <- cast $ premLits f
  vm <- mapSearch HM.empty fs gs
  pf <- usePrem (mapPremLit gs) vm f
  return $ pp $ NotF' s $ Cut' f (iffMP s f) pf
avatarCompCore _ _ = et "avatar-comp-core : not iff"

aoct :: [Term] -> [Text] -> VM -> Term -> Term -> IO VM
aoct zs ws vm (Var v) y@(Fun f xs) =
  case HM.lookup v vm of
    Just x -> guard (x == y) >> return vm
    _ -> guard (isPerm zs xs) >> return (HM.insert v y vm)
aoct zs ws vm x@(Fun f xs) y@(Fun g ys)
  | x == y = return vm
  | f == g = foldM2 (aoct zs ws) vm xs ys
  | otherwise = mzero
aoct zs ws vm x y
  | x == y = return vm
  | otherwise = mzero

aocf :: [Term] -> [Text] -> VM -> Form -> Form -> IO VM
aocf zs ws vm (Eq x y) (Eq z w) =
  foldM2 (aoct zs ws) vm [x, y] [z, w] <|> foldM2 (aoct zs ws) vm [x, y] [w, z]
aocf zs ws vm (Rel r xs) (Rel s ys) = do
  guard $ r == s
  foldM2 (aoct zs ws) vm xs ys
aocf zs us vm (Not f) (Not g) = aocf zs us vm f g
aocf zs us vm (Or fs) (Or gs) = foldM2 (aocf zs us) vm fs gs
aocf zs us vm (And fs) (And gs) = foldM2 (aocf zs us) vm fs gs
aocf zs us vm (Fa vs f) (Fa ws g) = do
  guard $ isPerm vs ws
  aocf zs (ws L.\\ vs) vm f g
aocf zs us vm (Ex vs f) (Ex ws g) = do
  guard $ isPerm vs ws
  aocf zs (ws L.\\ vs) vm f g
aocf zs ws vm f g = et "aocf : todo"

normalizeAoC :: Form -> IO ([Term], Form)
normalizeAoC (Fa vs (Imp (Ex ws f) g)) = do
  vm <- aocf (L.map Var vs) ws HM.empty  f g
  -- pt $ "VM =\n" <> ppVM vm 
  xs <- cast $ mapM (`HM.lookup` vm) ws
  return (xs, Fa vs (Imp (Ex ws f) (subf vm f)))
normalizeAoC (Imp (Ex ws f) g) = do
  vm <- aocf [] ws HM.empty f g
  xs <- cast $ mapM (`HM.lookup` vm) ws
  return (xs, Imp (Ex ws f) (subf vm f))
normalizeAoC _ = mzero

--mkRelD :: Text -> Form -> Maybe Form
--mkRelD r (Fa vs g) = do
--  f <- mkRelD r g
--  return (Fa vs f)
--mkRelD r (Iff (Rel s xs) f) = guard (r == s) >> return (Iff (Rel s xs) f)
--mkRelD r (Iff f (Rel s xs)) = guard (r == s) >> return (Iff (Rel s xs) f)
--mkRelD r (Or [f, Not (Rel s xs)]) = guard (r == s) >> return (Iff (Rel s xs) f)
--mkRelD r (Or fs) = do
--  (fs', Not (Rel s xs)) <- desnoc fs
--  guard (r == s)
--  return (Iff (Rel s xs) (Or fs'))
--mkRelD _ f = eb $ "Cannot make rdef :\n" <> ppFormNl f
mkRelD :: Form -> Maybe Form
mkRelD (Fa vs g) = do
  f <- mkRelD g
  return (Fa vs f)
mkRelD (Iff (Rel s xs) f) = return (Iff (Rel s xs) f)
mkRelD (Iff f (Rel s xs)) = return (Iff (Rel s xs) f)
mkRelD (Or [f, Not (Rel s xs)]) = return (Iff (Rel s xs) f)
mkRelD (Or fs) = do
  (fs', Not (Rel s xs)) <- desnoc fs
  return (Iff (Rel s xs) (Or fs'))
mkRelD f = eb $ "Cannot make rdef :\n" <> ppFormNl f

proveRelD' :: Form -> Form -> IO Prf
proveRelD' (Fa vs f) (Fa ws g) = do
  guard (vs == ws)
  let (_, xs) = listPars 0 vs
  vxs <- zipM vs xs
  p <- proveRelD'' (substForm vxs f) (substForm vxs g)
  return $ FaF' ws 0 g $ FaT' vxs f p
proveRelD' f g = proveRelD'' f g

proveRelD'' :: Form -> Form -> IO Prf
proveRelD'' f@(Iff fl fr) g@(Iff gl gr) =
  (guard (f == g) >> return (Id' f)) <|>
  (guard (fl == gr && fr == gl) >> return (iffSym fl fr))
proveRelD'' (Iff r b) (Or [b', Not r'])  = do
  guard (r == r' && b == b')
  return $ rDefLemma0 r b
proveRelD'' (Iff r (Or fs)) (Or fsnr)  = do
  (fs', Not r') <- cast $ desnoc fsnr
  guard (r == r' && fs == fs')
  return $ rDefLemma1 r fs fsnr
proveRelD'' f g = eb $ "Anomaly! : " <> ppForm f <> " |- " <> ppForm g <> "\n"

relDef :: Text -> Form -> IO Stelab
relDef n g = do
  f <- cast $ mkRelD g
  p <- proveRelD' f g
  return $ DefStep f g p n

pqm :: Int -> Form -> Form -> IO Prf
pqm k (Not f) (Not g) = do
  p <- pqm k f g
  return $ Cut' (f <=> g) p $ iffToNotIffNot f g
pqm k (Or fs) (Or gs) = do
  fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> pqm k f_ g_) fs gs
  cuts fgps <$> cast (iffsToOrIffOr fs gs)
pqm k (And fs) (And gs) = do
  fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> pqm k f_ g_) fs gs
  cuts fgps <$> cast (iffsToAndIffAnd fs gs)
pqm k (Imp e f) (Imp g h) = do
  pl <- pqm k e g -- pl : |- fl <=> gl 
  pr <- pqm k f h -- pl : |- fr <=> gr
  return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ impCong e f g h
pqm k (Iff e f) (Iff g h) = do
  pl <- pqm k e g -- pl : |- fl <=> gl 
  pr <- pqm k f h -- pl : |- fr <=> gr
  return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ iffCong e f g h
pqm k (Fa us (Fa vs f)) (Fa ws g) = do
  guard (us ++ vs == ws)
  let (k', wxs) = varPars k ws
  let f' = substForm wxs f
  let g' = substForm wxs g
  p <- pqm k' f' g'
  return $ 
    iffsTrans 
      [ (Fa us (Fa vs f), faFaIff k us vs f), 
        (Fa ws f, Cut' (Fa ws $ f <=> g) (FaF' ws k (f <=> g) p) $ faIffToFaIffFa ws k f g)] 
      (Fa ws g)
pqm k (Ex us (Ex vs f)) (Ex ws g) = do
  guard (us ++ vs == ws)
  let (k', wxs) = varPars k ws
  let f' = substForm wxs f
  let g' = substForm wxs g
  p <- pqm k' f' g'
  return $ 
    iffsTrans 
      [ (Ex us (Ex vs f), exExIff k us vs f), 
        (Ex ws f, Cut' (Fa ws $ f <=> g) (FaF' ws k (f <=> g) p) $ faIffToExIffEx ws k f g)] 
      (Ex ws g)
pqm k (Fa vs f) (Fa ws g) = do
  guard (vs == ws)
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let g' = substForm vxs g
  p <- pqm k' f' g'
  return $ Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) p) $ faIffToFaIffFa vs k f g
pqm k (Ex vs f) (Ex ws g) = do
  guard (vs == ws)
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let g' = substForm vxs g
  p <- pqm k' f' g'
  return $ Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) p) $ faIffToExIffEx vs k f g
pqm _ f g
  | f == g = return $ iffRefl f
  | otherwise = et "prove-quant-merge"

flattening :: Form -> Form -> IO Prf
flattening f g = do
  let f' = fltn f
  let f'' = dne f'
  guard $ qmerge f'' == g
  p0 <- pfl 0 f f'
  p1 <- pdne 0 f' f''
  p2 <- pqm 0 f'' g
  return $ cutIff f g (iffsTrans [(f, p0), (f', p1), (f'', p2)] g) $ Id' g

exSimp :: Int -> [Text] -> Form -> Form -> IO Prf
exSimp k vs (And []) (And []) = return $ exTopIff vs
exSimp k vs (Or []) (Or []) = return $ exBotIff k vs
exSimp k vs f (Ex ws g) = do 
  guardMsg "ex-simp" $ vs == ws && f == g
  return $ iffRefl (Ex vs f)
exSimp _ _ _ _ = et "ex-simp"

faSimp :: Int -> [Text] -> Form -> Form -> IO Prf
faSimp k vs (And []) (And []) = return $ faTopIff k vs
faSimp k vs (Or []) (Or []) = return $ faBotIff vs
faSimp k vs f (Fa ws g) = do 
  guardMsg "ex-simp" $ vs == ws && f == g
  return $ iffRefl (Fa vs f)
faSimp _ _ _ _ = et "fa-simp"

notSimp :: Form -> Form -> IO Prf
notSimp (And []) (Or []) = return $ iffRFull (Not top) bot (NotT' top $ AndF' []) (OrT' []) 
notSimp (Or []) (And []) = return $ iffRFull (Not bot) top (AndF' []) (NotF' bot $ OrT' []) 
notSimp f (Not g) = guard (f == g) >> return (iffRefl (Not f))
notSimp _ _ = et "not-simp"

iffSimp :: Form -> Form -> Form -> IO Prf
iffSimp f (And []) g = do
  guardMsg "iff-simp" $ f == g
  return $
    iffRFull (f <=> top) f
      (Cut' top (AndF' []) $ iffMPR f top)
      (iffRFull f top (AndF' []) (Id' f))
iffSimp (And []) f g = do
  guardMsg "iff-simp" $ f == g
  return $
    iffRFull (top <=> f) f
      (Cut' top (AndF' []) $ iffMP f top)
      (iffRFull top f (Id' f) (AndF' []))

iffSimp (Or []) f (Not g) = do 
  guardMsg "iff-simp" $ f == g
  return $
    iffRFull (bot <=> f) (Not f) 
      (NotF' f $ Cut' bot (iffMPR bot f) (OrT' []))
      (iffRFull bot f (OrT' []) (NotT' f $ Id' f))
iffSimp f (Or []) (Not g) = do 
  guardMsg "iff-simp" $ f == g
  return $
    iffRFull (f <=> bot) (Not f) 
      (NotF' f $ Cut' bot (iffMP f bot) (OrT' []))
      (iffRFull f bot (NotT' f $ Id' f) (OrT' []))
iffSimp f g (Iff f' g') = do
  guardMsg "iff-simp" $ f == f'
  guardMsg "iff-simp" $ g == g'
  return $ iffRefl (f <=> g)
iffSimp f g h = 
  eb $ 
    "iff-simp\n" <> 
    "f : " <> ppForm f <> "\n" <>
    "g : " <> ppForm g <> "\n" <>
    "h : " <> ppForm h <> "\n"

impSimp :: Form -> Form -> Form -> IO Prf
impSimp f (And []) (And []) = 
  return $
    iffRFull (f ==> top) top 
      (AndF' [])
      (ImpFC' top f $ AndF' [])
impSimp (Or []) f (And []) = 
  return $
    iffRFull (bot ==> f) top 
      (AndF' [])
      (ImpFA' bot f $ OrT' [])
impSimp f (Or []) (Not g) = do
  guardMsg "imp-simp" $ f == g
  return $
    iffRFull (f ==> bot) (Not f) 
      (NotF' f $ ImpT' f bot (Id' f) (OrT' [])) 
      (NotT' f $ ImpFA' f bot $ Id' f)
impSimp (And []) f g = do
  guardMsg "imp-simp" $ f == g
  return $
    iffRFull (top ==> f) f 
      (ImpT' top f (AndF' []) (Id' f)) 
      (ImpFC' top f $ Id' f)
impSimp f g (Imp f' g') = do
  guardMsg "imp-simp" $ f == f'
  guardMsg "imp-simp" $ g == g'
  return $ iffRefl (f ==> g)
impSimp f g h = 
  eb $ 
    "imp-simp\n" <> 
    "f : " <> ppForm f <> "\n" <>
    "g : " <> ppForm g <> "\n" <>
    "h : " <> ppForm h <> "\n"

pbs :: Int -> Form -> Form -> IO Prf
pbs k (Not f) h = do
  let g = boolSimp f 
  pfg <- pbs k f g
  pgh <- notSimp g h
  return $ iffsTrans [(Not f, Cut' (f <=> g) pfg $ iffToNotIffNot f g), (Not g, pgh)] h
pbs k (Or fs) (And []) = do
  let gs = L.map boolSimp fs 
  guardMsg "top not found" $ top `elem` gs
  fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> pbs k f_ g_) fs gs
  pfg <- cuts fgps <$> cast (iffsToOrIffOr fs gs)
  return $ iffsTrans [(Or fs, pfg), (Or gs, degenOrIff gs)] top
pbs k (And fs) (Or []) = do
  let gs = L.map boolSimp fs 
  guardMsg "bot not found" $ bot `elem` gs
  fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> pbs k f_ g_) fs gs
  pfg <- cuts fgps <$> cast (iffsToAndIffAnd fs gs)
  return $ iffsTrans [(And fs, pfg), (And gs, degenAndIff gs)] bot
-- pbs k (Or fs) h = do
--   let gs = L.map boolSimp fs 
--   let gs' = L.filter (not . isBot) gs 
--   fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> pbs k f_ g_) fs gs
--   pfg <- cuts fgps <$> cast (iffsToOrIffOr fs gs)
--   case (gs', h) of 
--     ([g], _) -> return $ iffsTrans [(Or fs, pfg), (Or gs, bloatOrIff' gs g)] h
--     (_, Or hs) -> return $ iffsTrans [(Or fs, pfg), (Or gs, bloatOrIff gs)] (Or hs)
--     _ -> et "pbs-or"
-- pbs k (And fs) h = do
--   let gs = L.map boolSimp fs 
--   let gs' = L.filter (not . isTop) gs 
--   fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> pbs k f_ g_) fs gs
--   pfg <- cuts fgps <$> cast (iffsToAndIffAnd fs gs)
--   case (gs', h) of 
--     ([g], _) -> return $ iffsTrans [(And fs, pfg), (And gs, bloatAndIff' gs g)] h
--     (_, And hs) -> return $ iffsTrans [(And fs, pfg), (And gs, bloatAndIff gs)] (And hs)
--     _ -> et "pbs-and"
pbs k (Or fs) (Or hs) = do
  let gs = L.map boolSimp fs 
  guardMsg "top filter mismatch" $ L.filter (not . isBot) gs == hs
  fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> pbs k f_ g_) fs gs
  pfg <- cuts fgps <$> cast (iffsToOrIffOr fs gs)
  return $ iffsTrans [(Or fs, pfg), (Or gs, bloatOrIff gs)] (Or hs)
pbs k (And fs) (And hs) = do
  let gs = L.map boolSimp fs 
  guardMsg "top filter mismatch" $ L.filter (not . isTop) gs == hs
  fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> pbs k f_ g_) fs gs
  pfg <- cuts fgps <$> cast (iffsToAndIffAnd fs gs)
  return $ iffsTrans [(And fs, pfg), (And gs, bloatAndIff gs)] (And hs)
pbs k (Imp f g) h = do
  let f' = boolSimp f
  let g' = boolSimp g
  pf <- pbs k f f' -- pl : |- fl <=> gl 
  pg <- pbs k g g' -- pl : |- fr <=> gr
  let pn = Cut' (f <=> f') pf $ Cut' (g <=> g') pg $ impCong f g f' g'
  ph <- impSimp f' g' h
  return $ iffsTrans [(Imp f g, pn), (Imp f' g', ph)] h

pbs k (Iff f g) h = do
  let f' = boolSimp f
  let g' = boolSimp g
  pf <- pbs k f f' -- pl : |- fl <=> gl 
  pg <- pbs k g g' -- pl : |- fr <=> gr
  let pn = Cut' (f <=> f') pf $ Cut' (g <=> g') pg $ iffCong f g f' g'
  ph <- iffSimp f' g' h
  return $ iffsTrans [(Iff f g, pn), (Iff f' g', ph)] h
pbs k (Fa vs f) h = do
  let g = boolSimp f
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let g' = substForm vxs g
  pfg <- pbs k' f' g'
  let pfg' = Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) pfg) (faIffToFaIffFa vs k f g)
  pgh <- faSimp k vs g h
  return $ iffsTrans [(Fa vs f, pfg'), (Fa vs g, pgh)] h
pbs k (Ex vs f) h = do
  let g = boolSimp f
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let g' = substForm vxs g
  pfg <- pbs k' f' g'
  let pfg' = Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) pfg) (faIffToExIffEx vs k f g)
  pgh <- exSimp k vs g h
  return $ iffsTrans [(Ex vs f, pfg'), (Ex vs g, pgh)] h
pbs _ f g
  | f == g = return $ iffRefl f
  | otherwise = eb $ "prove-bool-simp\nf : " <> ppForm f <> "\ng : " <> ppForm g <> "\n"

removePure :: Form -> Form -> IO Prf
removePure f g = do
  let rs = diffPreds f g
  let f1 = ppr rs True f
  let f2 = boolSimp f1
  let f3 = uws f2
  let f4 = fltn f3
  let f5 = qmerge f4
  guardMsg (tlt $ "PPR mismatch\nf' : " <> ppForm f5 <> "\ng :  " <> ppForm g <> "\n") (f5 == g)
  p1 <- ppp 0 f f1
  p2 <- pbs 0 f1 f2
  p3 <- puw 0 f2 f3
  p4 <- pfl 0 f3 f4
  p5 <- pqm 0 f4 f5
  let p = iffsTrans [(f1, p2), (f2, p3), (f3, p4), (f4, p5)] f5
  return $ Cut' f1 p1 $ Cut' (f1 <=> f5) p $ iffMP f1 f5

puw :: Int -> Form -> Form -> IO Prf
puw k (Not f) (Not g) = do
  p <- puw k f g
  return $ Cut' (f <=> g) p $ iffToNotIffNot f g
puw k (Or [f]) g = do 
  p <- puw k f g
  return $ iffsTrans [(Or [f], singleOrIff f), (f, p)] g
puw k (Or fs) (Or gs) = do
  fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> puw k f_ g_) fs gs
  cuts fgps <$> cast (iffsToOrIffOr fs gs)
puw k (And [f]) g = do 
  p <- puw k f g
  return $ iffsTrans [(And [f], singleAndIff f), (f, p)] g
puw k (And fs) (And gs) = do
  fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> puw k f_ g_) fs gs
  cuts fgps <$> cast (iffsToAndIffAnd fs gs)
puw k (Imp e f) (Imp g h) = do
  pl <- puw k e g -- pl : |- fl <=> gl 
  pr <- puw k f h -- pl : |- fr <=> gr
  return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ impCong e f g h
puw k (Iff e f) (Iff g h) = do
  pl <- puw k e g -- pl : |- fl <=> gl 
  pr <- puw k f h -- pl : |- fr <=> gr
  return $ Cut' (e <=> g) pl $ Cut' (f <=> h) pr $ iffCong e f g h
puw k (Fa vs f) (Fa ws g) = do
  guard (vs == ws)
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let g' = substForm vxs g
  p <- puw k' f' g'
  return $ Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) p) $ faIffToFaIffFa vs k f g
puw k (Ex vs f) (Ex ws g) = do
  guard (vs == ws)
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let g' = substForm vxs g
  p <- puw k' f' g'
  return $ Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) p) $ faIffToExIffEx vs k f g
puw _ f g
  | f == g = return $ iffRefl f
  | otherwise = et "prove-DNE"

skolemize :: [Form] -> Int -> Form -> Form -> IO Prf
skolemize fs k f g 
  | f == g = return $ Id' f 
  | otherwise =
    case first (skolAux f) fs of 
      Just (f', p0) -> do 
        p1 <- skolemize fs k f' g
        return $ Cut' f' p0 p1
      _ -> skol fs k f g

skolAux :: Form -> Form -> Maybe (Form, Prf)
skolAux f (Imp g h) 
  | f == g = return (h, mp g h)
skolAux f (Fa vs (Imp g h)) = do 
  vm <- fspec HM.empty g f
  vxs <- mapM (\ v_ -> (v_,) <$> HM.lookup v_ vm) vs 
  let g' = substForm vxs g
  let h' = substForm vxs h 
  return (h', FaT' vxs (Imp g h) $ mp g' h')
skolAux _ _ = mzero

skol :: [Form] -> Int -> Form -> Form -> IO Prf
skol fs k (Fa vs f) (Fa ws g) = do
  guardMsg "skol : not permutation" $ isPerm vs ws
  let (k', wxs) = varPars k ws 
  vxs <- cast $ mapM (\ v_ -> L.find ((v_ ==) . fst) wxs) vs
  let f' = substForm vxs f
  let g' = substForm wxs g
  p <- skolemize fs k' f' g'
  return $ FaF' ws k g $ FaT' vxs f p
skol ds k (And fs) (And gs) = do
  gps <- mapM2 (\ f_ g_ -> (g_,) <$> skolemize ds k f_ g_) fs gs
  return $ AndT' fs fs $ AndF' gps
skol ds k (Or fs) (Or gs) = do
  fps <- mapM2 (\ f_ g_ -> (f_,) <$> skolemize ds k f_ g_) fs gs
  return $ OrF' gs gs $ OrT' fps
skol fs k f g = do
  eb $ "skol\n" <>
       "fs :\n" <>
       ppListNl ppForm fs <> "\n" <>
       "f : " <> ppForm f <> "\n" <>
       "g : " <> ppForm g <> "\n"

updr :: Int -> Form -> Form -> IO Prf
updr k (Fa vs f) (Fa ws g) = do 
  guardMsg "UPDR : vars mismatch" $ vs == ws
  let (k', vxs) = varPars k vs 
  let f' = substForm vxs f
  let g' = substForm vxs g
  p <- updr k' f' g'
  return $ FaF' vs k g $ FaT' vxs f p
updr k (Iff e f) (Imp g h) 
  | e == g && f == h = return $ IffTO' e f $ Id' (e ==> f)  
  | e == h && f == g = return $ IffTR' e f $ Id' (f ==> e)
  | otherwise = et "not an iff component"
updr k f g = eb $
  "UPDR\n" <>
  "f : " <> ppForm f <> "\n" <>
  "g : " <> ppForm g <> "\n" 

nnfTrans :: Bool -> Form -> Form -> IO Prf
nnfTrans b f g = do 
  p <- pnnf b 0 f g 
  return $ Cut' (f <=> g) p $ iffMP f g

trueFalseElim :: Form -> Form -> IO Prf
trueFalseElim f g = do 
  let f' = boolSimp f
  let f'' = uws f'
  guard $ f'' == g
  p0 <- pbs 0 f f'
  p1 <- puw 0 f' f''
  return $ cutIff f f' p0 $ cutIff f' f'' p1 $ Id' g

pnnf :: Bool -> Int -> Form -> Form -> IO Prf
pnnf b k (Not (Not f)) g = do 
  p <- pnnf b k f g 
  return $ iffsTrans [(Not (Not f), notNotIff f), (f, p)] g
pnnf b k (Not (Or fs)) (And gs) = do
  let nfs = L.map Not fs 
  nfgps <- mapM2 (\ nf_ g_ -> (nf_ <=> g_,) <$> pnnf b k nf_ g_) nfs gs
  p <- cuts nfgps <$> cast (iffsToAndIffAnd nfs gs)
  return $ iffsTrans [(Not (Or fs), notOrIffAndNots fs), (And nfs, p)] (And gs)
pnnf b k (Not (And fs)) (Or gs) = do
  let nfs = L.map Not fs 
  nfgps <- mapM2 (\ nf_ g_ -> (nf_ <=> g_,) <$> pnnf b k nf_ g_) nfs gs
  p <- cuts nfgps <$> cast (iffsToOrIffOr nfs gs)
  return $ iffsTrans [(Not (And fs), notAndIffOrNots fs), (Or nfs, p)] (Or gs)
pnnf b k (Not (Imp f g)) h = do
  p <- pnnf b k (And [Not g, f]) h
  return $ iffsTrans [(Not (Imp f g), notImpIffNotAnd f g), (And [Not g, f], p)] h
pnnf True k (Not (Iff f g)) (Not fg) = do
  p <- pnnf True k (f <=> g) fg
  return $ Cut' ((f <=> g) <=> fg) p $ iffToNotIffNot (f <=> g) fg
pnnf False k (Not (Iff f g)) (And [Or [ng', nf'], Or [g', f']]) = do 
  png <- pnnf False k (Not g) ng'
  pnf <- pnnf False k (Not f) nf'
  pf <- pnnf False k f f'
  pg <- pnnf False k g g'
  _px <- cast $ iffsToOrIffOr [Not g, Not f] [ng', nf']
  let px = Cut' (Not g <=> ng') png $ Cut' (Not f <=> nf') pnf _px -- px |- Or [Not g, Not f] <=> Or [ng', nf']
  _py <- cast $ iffsToOrIffOr [g, f] [g', f']
  let py = Cut' (g <=> g') pg $ Cut' (f <=> f') pf _py -- py |- Or [g, f] <=> Or [g', f']
  _pz <- cast $ iffsToAndIffAnd [Or [Not g, Not f], Or [g, f]] [Or [ng', nf'], Or [g', f']]
  let pz = Cut' (Or [Not g, Not f] <=> Or [ng', nf']) px $ Cut' (Or [g, f] <=> Or [g', f']) py _pz -- pz : |- (And [Or [Not g, Not f], Or [g, f]], pz) <=> (And [Or [ng', nf'], Or [g', f']]) 
  return $ 
    iffsTrans 
      [ (Not (Iff f g), notIffIffAnd f g), 
        (And [Or [Not g, Not f], Or [g, f]], pz) ] 
    (And [Or [ng', nf'], Or [g', f']]) 

pnnf b k (Not (Fa vs f)) (Ex ws nf) = do 
  guard $ vs == ws
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let nf' = substForm vxs nf
  pnf <- pnnf b k' (Not f') nf'
  let p = Cut' (Fa vs $ Not f <=> nf) (FaF' vs k (Not f <=> nf) pnf) $ faIffToExIffEx vs k (Not f) nf
  return $ iffsTrans [(Not (Fa vs f), notFaIffExNot k vs f), (Ex vs (Not f), p)] (Ex ws nf)

pnnf b k (Not (Ex vs f)) (Fa ws nf) = do 
  guard $ vs == ws
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let nf' = substForm vxs nf
  pnf <- pnnf b k' (Not f') nf'
  let p = Cut' (Fa vs $ Not f <=> nf) (FaF' vs k (Not f <=> nf) pnf) $ faIffToFaIffFa vs k (Not f) nf
  return $ iffsTrans [(Not (Ex vs f), notExIffFaNot k vs f), (Fa vs (Not f), p)] (Fa ws nf)

pnnf b k (Fa vs f) (Fa ws g) = do 
  guard $ vs == ws
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let g' = substForm vxs g
  p <- pnnf b k' f' g'
  return $ Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) p) $ faIffToFaIffFa vs k f g

pnnf b k (Ex vs f) (Ex ws g) = do 
  guard $ vs == ws
  let (k', vxs) = varPars k vs
  let f' = substForm vxs f
  let g' = substForm vxs g
  p <- pnnf b k' f' g'
  return $ Cut' (Fa vs $ f <=> g) (FaF' vs k (f <=> g) p) $ faIffToExIffEx vs k f g

pnnf b k (Imp f g) (Or [g', nf']) = do 
  pf <- pnnf b k (Not f) nf'
  pg <- pnnf b k g g'
  _p <- cast $ iffsToOrIffOr [g, Not f] [g', nf']
  let p = cuts [(Not f <=> nf', pf), (g <=> g', pg)] _p
  return $ iffsTrans [(f ==> g, impIffOrNot f g), (Or [g, Not f], p)] (Or [g', nf'])

pnnf b k (And fs) (And gs) = do
  fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> pnnf b k f_ g_) fs gs
  cuts fgps <$> cast (iffsToAndIffAnd fs gs)
pnnf b k (Or fs) (Or gs) = do
  fgps <- mapM2 (\ f_ g_ -> (f_ <=> g_,) <$> pnnf b k f_ g_) fs gs
  cuts fgps <$> cast (iffsToOrIffOr fs gs)
pnnf True k (Iff f g) (Iff f' g') = do
  pf <- pnnf True k f f'
  pg <- pnnf True k g g'
  return $ Cut' (f <=> f') pf $ Cut' (g <=> g') pg $ iffCong f g f' g' 
pnnf False k (Iff f g) (And [Or [f', ng'], Or [g', nf']]) = do 
  png <- pnnf False k (Not g) ng'
  pnf <- pnnf False k (Not f) nf'
  pf <- pnnf False k f f'
  pg <- pnnf False k g g'
  _px <- cast $ iffsToOrIffOr [f, Not g] [f', ng']
  let px = Cut' (f <=> f') pf $ Cut' (Not g <=> ng') png _px -- px |- Or [f, Not g] <=> Or [f', ng']
  _py <- cast $ iffsToOrIffOr [g, Not f] [g', nf']
  let py = Cut' (g <=> g') pg $ Cut' (Not f <=> nf') pnf _py -- py |- Or [g, Not f] <=> Or [g', nf']
  _pz <- cast $ iffsToAndIffAnd [Or [f, Not g], Or [g, Not f]] [Or [f', ng'], Or [g', nf']]
  let pz = Cut' (Or [f, Not g] <=> Or [f', ng']) px $ Cut' (Or [g, Not f] <=> Or [g', nf']) py _pz 
  return $ 
    iffsTrans 
      [ (Iff f g, iffIffAnd f g), 
        (And [Or [f, Not g], Or [g, Not f]], pz) ] 
    (And [Or [f', ng'], Or [g', nf']]) 
pnnf _ _ f@(Not (Rel _ _)) g
  | f == g = return $ iffRefl f
pnnf _ _ f@(Not (Eq _ _)) g
  | f == g = return $ iffRefl f
pnnf _ _ f@(Rel _ _) g
  | f == g = return $ iffRefl f
pnnf _ _ f@(Eq _ _) g
  | f == g = return $ iffRefl f
pnnf _ _ f g = eb $ "prove-nnf\nf : " <> ppForm f <> "\ng : " <> ppForm g <> "\n"