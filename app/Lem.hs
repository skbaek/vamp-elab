{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module Lem where

import Types
import LocalTypes
import Basic
import Data.List
import qualified Data.ByteString as BS
import Data.Map as HM (Map, lookup)

mt :: Form -> Form -> Prf -- f => g |- ~g => ~f
mt f g = ImpT' f g (ImpFC' (Not g) (Not f) $ NotF' f $ Id' f) (ImpFA' (Not g) (Not f) $ NotT' g $ Id' g)

impRefl :: Form -> Prf
impRefl f = ImpFA' f f $ ImpFC' f f $ Id' f

-- impToOrNot f g : (f ==> g) |- (g \/ ~f)
impToOrNot :: Form -> Form -> Prf
impToOrNot f g = OrF' [g, Not f] [g, Not f] $ NotF' f $ ImpT' f g (Id' f) (Id' g)

-- orNotToImp f g : (g \/ ~f) |- (f ==> g) 
orNotToImp :: Form -> Form -> Prf
orNotToImp f g = impFAC f g $ OrT' [(g, Id' g), (Not f, NotT' f $ Id' f)]

-- impIffOrNot vs f f : |- (f ==> g) <=> (g \/ ~f)
impIffOrNot :: Form -> Form -> Prf
impIffOrNot f g = iffRFull (f ==> g) (Or [g, Not f]) (impToOrNot f g) (orNotToImp f g)

-- iffIffAnd f g : |- (f <=> g) <=> ((f \/ ~g) /\ (g \/ ~f))
iffIffAnd :: Form -> Form -> Prf
iffIffAnd f g = 
  iffRFull (f <=> g) (And [Or [f, Not g], Or [g, Not f]])
    (AndF' [(Or [f, Not g], IffTR' f g $ impToOrNot g f), (Or [g, Not f], IffTO' f g $ impToOrNot f g)])
    (AndT' [Or [f, Not g], Or [g, Not f]] [Or [f, Not g], Or [g, Not f]] $ IffF' f g (orNotToImp f g) (orNotToImp g f))

-- notFaIffExNot vs f : |- ~(! vs f) <=> ? vs (~ f)
notFaIffExNot :: Int -> [BS] -> Form -> Prf
notFaIffExNot k vs f = 
  let (_, vxs) = varPars k vs in
  let ks = rangeOver k vs in
  let f' = substForm vxs f in
  iffRFull (Not (Fa vs f)) (Ex vs (Not f)) 
    (NotT' (Fa vs f) $ FaF' vs ks f $ ExF' vxs (Not f) $ NotF' f' $ Id' f') 
    (NotF' (Fa vs f) $ ExT' vs ks (Not f) $ FaT' vxs f $ NotT' f' $ Id' f')

-- notFaIffExNot vs f : |- ~(? vs f) <=> ! vs (~ f)
notExIffFaNot :: Int -> [BS] -> Form -> Prf
notExIffFaNot k vs f = 
  let (_, vxs) = varPars k vs in
  let ks = rangeOver k vs in
  let f' = substForm vxs f in
  iffRFull (Not (Ex vs f)) (Fa vs (Not f)) 
    (NotT' (Ex vs f) $ FaF' vs ks (Not f) $ ExF' vxs f $ NotF' f' $ Id' f') 
    (NotF' (Ex vs f) $ ExT' vs ks f $ FaT' vxs (Not f) $ NotT' f' $ Id' f')

-- notOrIffAndNots fs : |- ~(\/ fs) <=> /\ (~fs)
notOrIffAndNots :: [Form] -> Prf
notOrIffAndNots fs = 
  let nfs = map Not fs in
  let nfps = map (\ f_ -> (Not f_, NotF' f_ (Id' f_))) fs in
  let fps = map (\ f_ -> (f_, NotT' f_ (Id' f_))) fs in
  iffRFull (Not $ Or fs) (And nfs) 
    (NotT' (Or fs) $ OrF' fs fs $ AndF' nfps) 
    (NotF' (Or fs) $ AndT' nfs nfs $ OrT' fps)

-- notAndIffOrNots fs : |- ~(/\ fs) <=> \/ (~fs)
notAndIffOrNots :: [Form] -> Prf
notAndIffOrNots fs = 
  let nfs = map Not fs in
  let nfps = map (\ f_ -> (Not f_, NotT' f_ (Id' f_))) fs in
  let fps = map (\ f_ -> (f_, NotF' f_ (Id' f_))) fs in
  iffRFull (Not $ And fs) (Or nfs) 
    (NotT' (And fs) $ OrF' nfs nfs $ AndF' fps) 
    (NotF' (And fs) $ AndT' fs fs $ OrT' nfps)

-- notImpIffNotand f g : |- ~(f ==> g) <=> (~g /\ f)
notImpIffNotAnd :: Form -> Form -> Prf
notImpIffNotAnd f g = 
  iffRFull (Not (f ==> g)) (And [Not g, f]) 
    (NotT' (f ==> g) $ AndF' [(Not g, NotF' g $ ImpFC' f g $ Id' g), (f, ImpFA' f g $ Id' f)]) 
    (AndT' [Not g, f] [Not g, f] $ NotT' g $ NotF' (f ==> g) $ ImpT' f g (Id' f) (Id' g))

mp :: Form -> Form -> Prf
mp f g = ImpT' f g (Id' f) (Id' g)

iffMP :: Form -> Form -> Prf  -- iffMP f g :  f <=> g, f |- g
iffMP f g = IffTO' f g $ mp f g

iffMPR :: Form -> Form -> Prf -- iffMPR f g : f <=> g, g |- f
iffMPR f g = IffTR' f g $ mp g f

iffToNotIffNot :: Form -> Form -> Prf -- f <=> g |- ~f <=> ~ g
iffToNotIffNot f g = 
  let pl = IffTR' f g (mt g f) in  
  let pr = IffTO' f g (mt f g) in
  IffF' (Not f) (Not g) pl pr 

impFAC :: Form -> Form -> Prf -> Prf
impFAC f g = ImpFA' f g . ImpFC' f g

-- iffsToOrIffOr : f0 <=> g0, ..., fn <=> gn |- (f0 \/ ... \/ fn) <=> (g0 \/ ... \/ gn)
iffsToOrIffOr :: [Form] -> [Form] -> Maybe Prf
iffsToOrIffOr fs gs = do
  fgs <- zipM fs gs
  let fps = map (\ (f_, g_) -> (f_, iffMP f_ g_)) fgs 
  let gps = map (\ (f_, g_) -> (g_, iffMPR f_ g_)) fgs 
  return $ iffRFull (Or fs) (Or gs) (OrF' gs gs $ OrT' fps) (OrF' fs fs $ OrT' gps)

-- iffsToOrIffOr : f0 <=> g0, ..., fn <=> gn |- (f0 \/ ... \/ fn) <=> (g0 \/ ... \/ gn)
iffsToOrIffOr' :: [(Form, Form)] -> [Form] -> [Form] -> Maybe Prf
iffsToOrIffOr' fgs fs gs = do
  fps <- mapM (\ f_ -> find ((f_ ==) . fst) fgs >>= \ (_, g_) -> return (f_, iffMP f_ g_)) fs 
  gps <- mapM (\ g_ -> find ((g_ ==) . snd) fgs >>= \ (f_, _) -> return (g_, iffMPR f_ g_)) gs 
  return $ iffRFull (Or fs) (Or gs) (OrF' gs gs $ OrT' fps) (OrF' fs fs $ OrT' gps)

-- iffsToAndIffAnd : f0 <=> g0, ..., fn <=> gn |- (f0 /\ ... /\ fn) <=> (g0 /\ ... /\ gn)
iffsToAndIffAnd :: [Form] -> [Form] -> Maybe Prf
iffsToAndIffAnd fs gs = do
  fgs <- zipM fs gs
  let fps = map (\ (f_, g_) -> (f_, iffMPR f_ g_)) fgs 
  let gps = map (\ (f_, g_) -> (g_, iffMP  f_ g_)) fgs 
  return $ iffRFull (And fs) (And gs) (AndT' fs fs $ AndF' gps) (AndT' gs gs $ AndF' fps) 

iffsToAndIffAnd' :: [(Form, Form)] -> [Form] -> [Form] -> Maybe Prf
iffsToAndIffAnd' fgs fs gs = do
  -- let fps = map (\ (f_, g_) -> (f_, iffMPR f_ g_)) fgs 
  fps <- mapM (\ f_ -> find ((f_ ==) . fst) fgs >>= \ (_, g_) -> return (f_, iffMPR f_ g_)) fs 
  gps <- mapM (\ g_ -> find ((g_ ==) . snd) fgs >>= \ (f_, _) -> return (g_, iffMP f_ g_)) gs 
  return $ iffRFull (And fs) (And gs) (AndT' fs fs $ AndF' gps) (AndT' gs gs $ AndF' fps) 

-- impTrans f g h : f ==> g, g ==> h |- f ==> h
impTrans ::  Form -> Form -> Form -> Prf
impTrans f g h = impFAC f h $ ImpT' f g (Id' f) $ ImpT' g h (Id' g) (Id' h)

-- impTrans3 e f g h : e ==> f, f ==> g, g ==> h |- e ==> h
impTrans3 :: Form -> Form -> Form -> Form -> Prf
impTrans3 e f g h = Cut' (f ==> h) (impTrans f g h) (impTrans e f h)

-- iffRefl f : |- f <=> f
iffRefl :: Form -> Prf 
iffRefl f = IffF' f f (impRefl f) (impRefl f)

-- iffSym f g : f <=> g |- g <=> f
iffSym :: Form -> Form -> Prf 
iffSym f g = IffF' g f (IffTR' f g $ Id' (g ==> f)) (IffTO' f g $ Id' (f ==> g))

-- iffTrans f g h : f <=> g, g <=> h |- f <=> h
iffTrans ::  Form -> Form -> Form -> Prf
iffTrans f g h = 
  let po = IffTO' f g $ IffTO' g h $ impTrans f g h in
  let pr = IffTR' f g $ IffTR' g h $ impTrans h g f in
  IffF' f h po pr 

-- e <=> f, e <=> g, f <=> h |- g <=> h
iffCongLem :: Form -> Form -> Form -> Form -> Prf
iffCongLem e f g h = Cut'(g <=> e) (iffSym e g) $ Cut'(e <=> h) (iffTrans e f h) $ iffTrans g e h

-- e <=> g, f <=> h |- (e <=> f) <=> (g <=> h)
iffCong :: Form -> Form -> Form -> Form -> Prf
iffCong e f g h = 
  IffF' (e <=> f) (g <=> h) 
    (impFAC (e <=> f) (g <=> h) $ iffCongLem e f g h) 
    (impFAC (g <=> h) (e <=> f) $ Cut'(g <=> e) (iffSym e g) $ Cut'(h <=> f) (iffSym f h) $ iffCongLem g h e f)

-- e <=> g, f <=> h |- (e ==> f) <=> (g ==> h)
impCong :: Form -> Form -> Form -> Form -> Prf
impCong e f g h = 
  IffF' (e ==> f) (g ==> h) 
  (impFAC (e ==> f) (g ==> h) $ Cut'(g ==> e) (IffTR' e g $ Id' (g ==> e)) $ Cut'(f ==> h) (IffTO' f h $ Id' (f ==> h)) $ impTrans3 g e f h) 
  (impFAC (g ==> h) (e ==> f) $ Cut'(e ==> g) (IffTO' e g $ Id' (e ==> g)) $ Cut'(h ==> f) (IffTR' f h $ Id' (h ==> f)) $ impTrans3 e g h f)

-- requires : none of vs occurs in f
-- bloatFaIff k vs f : |- (! vs f) <=> f
bloatFaIff :: Int -> [BS] -> Form -> Prf 
bloatFaIff k vs f = 
  let vxs = map (, zt) vs in
  let ks = rangeOver k vs in
  iffRFull (Fa vs f) f (FaT' vxs f $ Id' f) (FaF' vs ks f $ Id' f)

-- requires : none of vs occurs in f
-- bloatExIff k vs f : |- (? vs f) <=> f
bloatExIff :: Int -> [BS] -> Form -> Prf 
bloatExIff k vs f = 
  let vxs = map (, zt) vs in
  let ks = rangeOver k vs in
  iffRFull (Ex vs f) f (ExT' vs ks f $ Id' f) (ExF' vxs f $ Id' f)

degenHelper :: [(BS, Term)] -> BS -> (BS, Term)
degenHelper vxs w = 
  case find ((w ==) . fst) vxs of 
    Just (_, x) -> (w, x) 
    _ -> (w, zt) 

-- requires : ws is a subset of vs 
-- requires : none of (vs \ ws) occurs in f
-- bloatFaIffFa k vs ws f : |- (! vs f) <=> (! ws f)
bloatFaIffFa :: Int -> [BS] -> [BS] -> Form -> Prf 
bloatFaIffFa k vs ws f = 
  let (_, vxs) = varPars k vs in
  let vks = rangeOver k vs in
  let wks = rangeOver k ws in
  let (_, wxs) = varPars k ws in
  let vxs' = map (degenHelper wxs) vs in
  let wxs' = map (degenHelper vxs) ws in
  let fv = substForm vxs f in
  let fw = substForm wxs f in
  iffRFull (Fa vs f) (Fa ws f) 
    (FaF' ws wks f $ FaT' vxs' f $ Id' fw) 
    (FaF' vs vks f $ FaT' wxs' f $ Id' fv)

-- requires : ws is a subset of vs 
-- requires : none of (vs \ ws) occurs in f
-- bloatExIffEx k vs ws f : |- (? vs f) <=> (? ws f)
bloatExIffEx :: Int -> [BS] -> [BS] -> Form -> Prf 
bloatExIffEx k vs ws f = 
  let (_, vxs) = varPars k vs in
  let ks = rangeOver k vs in
  let (_, wxs) = varPars k ws in
  let vxs' = map (degenHelper wxs) vs in
  let wxs' = map (degenHelper vxs) ws in
  let fv = substForm vxs f in
  let fw = substForm wxs f in
  iffRFull (Ex vs f) (Ex ws f) (ExT' vs ks f $ ExF' wxs' f $ Id' fv) (ExT' ws ks f $ ExF' vxs' f $ Id' fw)

-- p : f' |- g'
---------------
-- exImpEx vs k f g p |- (? vs f) ==> (? vs g)
exImpEx :: [BS] -> Int -> Form -> Form -> Prf -> Prf
exImpEx vs k f g p = 
  let (_, vxs) = varPars k vs in
  let ks = rangeOver k vs in
  let f' = substForm vxs f in
  let g' = substForm vxs g in
  impFAC (Ex vs f) (Ex vs g) $ ExT' vs ks f $ ExF' vxs g p

-- p : f' |- g'
---------------
-- faImpFa vs k f g p : |- (! vs f) ==> (! vs g)
faImpFa :: [BS] -> Int -> Form -> Form -> Prf -> Prf
faImpFa vs k f g p = 
  let (_, vxs) = varPars k vs in
  let ks = rangeOver k vs in
  let f' = substForm vxs f in
  let g' = substForm vxs g in
  impFAC (Fa vs f) (Fa vs g) $ FaF' vs ks g $ FaT' vxs f p

-- ! vs (f <=> g) |- (? ws f) <=> (? ws g)
faIffToExIffEx' :: Int -> [BS] -> Form -> [BS] -> Form -> IO Prf
faIffToExIffEx' k vs f ws g = do
  let (_, vxs) = varPars k vs 
  let ks = rangeOver k vs
  let (_, wxs) = varPars k ws 
  wxs' <- mapM (\ w_ -> cast (find ((w_ ==) . fst) vxs)) ws
  vxs' <- mapM (\ v_ -> cast (find ((v_ ==) . fst) wxs)) vs
  let f' = substForm vxs f 
  let g' = substForm wxs g 
  let f'' = substForm vxs' f 
  let g'' = substForm wxs' g 
  return $ iffRFull (Ex vs f) (Ex ws g) 
    (ExT' vs ks f $ ExF' wxs' g $ FaT' vxs (f <=> g) $ iffMP f' g'') 
    (ExT' ws ks g $ ExF' vxs' f $ FaT' vxs' (f <=> g) $ iffMPR f'' g')

-- ! ws (f[vs |=> ws] <=> g) |- (? vs f) <=> (? ws g)
faIffToExIffEx'' :: Int -> [BS] -> Form -> [BS] -> Form -> IO Prf
faIffToExIffEx'' k vs f ws g = do
  let (_, vxs) = varPars k vs 
  let ks = rangeOver k vs 
  let (_, wxs) = varPars k ws 
  vws <- mapM2 (\ v_ w_ -> return (v_, Var w_)) vs ws
  let f' = substForm vxs f 
  let f'' = substForm vws f 
  let g' = substForm wxs g 
  return $ iffRFull (Ex vs f) (Ex ws g) 
    (ExT' vs ks f $ ExF' wxs g $ FaT' wxs (f'' <=> g) $ iffMP f' g') 
    (ExT' ws ks g $ ExF' vxs f $ FaT' wxs (f'' <=> g) $ iffMPR f' g')

-- ! ws (f[vw] <=> g) |- (? vs f) <=> (? ws g)
genFaIffToExIffEx :: Form -> VR -> Int -> [BS] -> Form -> [BS] -> Form -> IO Prf
genFaIffToExIffEx rfp (vw, wv) k vs f ws g = do
  let (_, vxs) = varPars k vs 
  let ks = rangeOver k vs 
  let (_, wxs) = varPars k ws 
  vxs' <- mapM (cast . findEqvInst vw wxs) vs
  wxs' <- mapM (cast . findEqvInst wv vxs) ws
  let f' = substForm vxs f 
  let g' = substForm wxs g 
  let f'' = substForm vxs' f 
  let g'' = substForm wxs' g 
  vws <- mapM (pairWithVR' (vw, wv)) vs 
  let fp = substForm vws f
  return $ iffRFull (Ex vs f) (Ex ws g) 
    (ExT' vs ks f $ ExF' wxs' g $ FaT' wxs' (fp <=> g) $ iffMP  f' g'') 
    (ExT' ws ks g $ ExF' vxs' f $ FaT' wxs  (fp <=> g) $ iffMPR f'' g')

-- ! ws (f[vs |=> ws] <=> g) |- (! vs f) <=> (! ws g)
faIffToFaIffFa'' :: Int -> [BS] -> Form -> [BS] -> Form -> IO Prf
faIffToFaIffFa'' k vs f ws g = do
  let (_, vxs) = varPars k vs 
  let ks = rangeOver k vs 
  let (_, wxs) = varPars k ws 
  vws <- mapM2 (\ v_ w_ -> return (v_, Var w_)) vs ws
  let f' = substForm vxs f 
  let f'' = substForm vws f 
  let g' = substForm wxs g 
  return $ iffRFull (Fa vs f) (Fa ws g) 
    (FaF' ws ks g $ FaT' vxs f $ FaT' wxs (f'' <=> g) $ iffMP f' g') 
    (FaF' vs ks f $ FaT' wxs g $ FaT' wxs (f'' <=> g) $ iffMPR f' g')

-- ! vs (f <=> g) |- (! vs f) <=> (! ws g)
faIffToFaIffFa' :: Int -> [BS] -> Form -> [BS] -> Form -> IO Prf
faIffToFaIffFa' k vs f ws g = do
  let (_, vxs) = varPars k vs 
  let ks = rangeOver k vs 
  let (_, wxs) = varPars k ws 
  wxs' <- mapM (\ w_ -> cast (find ((w_ ==) . fst) vxs)) ws
  vxs' <- mapM (\ v_ -> cast (find ((v_ ==) . fst) wxs)) vs
  let f' = substForm vxs f 
  let g' = substForm wxs g 
  let f'' = substForm vxs' f 
  let g'' = substForm wxs' g 
  return $ iffRFull (Fa vs f) (Fa ws g) 
    (FaF' ws ks g $ FaT' vxs' f $ FaT' vxs' (f <=> g) $ iffMP f'' g') 
    (FaF' vs ks f $ FaT' wxs' g $ FaT' vxs  (f <=> g) $ iffMPR f' g'')

findEqvInst :: HM.Map BS BS -> [(BS, Term)] -> BS -> Maybe (BS, Term)
findEqvInst vw wxs v = do 
  w <- HM.lookup v vw 
  (_, x) <- find ((w ==) . fst) wxs
  return (v, x)

-- ! ws (f[vw] <=> g) |- (! vs f) <=> (! ws g)
genFaIffToFaIffFa :: VR -> Int -> [BS] -> Form -> [BS] -> Form -> IO Prf
genFaIffToFaIffFa (vw, wv) k vs f ws g = do
  let (_, vxs) = varPars k vs 
  let ks = rangeOver k vs 
  let (_, wxs) = varPars k ws 
  vxs' <- mapM (cast . findEqvInst vw wxs) vs
  wxs' <- mapM (cast . findEqvInst wv vxs) ws
  let f' = substForm vxs f 
  let g' = substForm wxs g 
  let f'' = substForm vxs' f 
  let g'' = substForm wxs' g 
  -- let fp = appVrForm (vw, wv) f
  vws <- mapM (pairWithVR' (vw, wv)) vs 
  let fp = substForm vws f
  return $ iffRFull (Fa vs f) (Fa ws g) 
    (FaF' ws ks g $ FaT' vxs' f $ FaT' wxs  (fp <=> g) $ iffMP  f'' g' ) 
    (FaF' vs ks f $ FaT' wxs' g $ FaT' wxs' (fp <=> g) $ iffMPR f'  g'')

-- -- ! ws (f' <=> g) |- (? vs f) <=> (? ws g)
-- genFaIffToExIffEx' :: Int -> [BS] -> [Term] -> Form -> Form -> [BS] -> [Term] -> Form -> IO Prf
-- genFaIffToExIffEx' k vs xs f fr ws ys g = do 
--   vxs <- zipM vs xs
--   wys <- zipM ws ys
--   let f' = substForm vxs f 
--   let fr' = substForm wys f 
--   let g' = substForm wys g 
--   guardMsg "Substitution mismatch" $ f' == fr'
--   return $ iffRFull (Ex vs f) (Ex ws g) 
--     (ExT' vs k f $ ExF' wxs' g $ FaT' wxs' (fp <=> g) $ iffMP  f'' g' ) 
--     (ExT' ws k g $ ExF' vxs' f $ FaT' wxs  (fp <=> g) $ iffMPR f'  g'')

-- faFaIff k vs ws f : |- ! vs (! ws f) <=> ! (vs ++ ws) f
faFaIff :: Int -> [BS] -> [BS] -> Form -> Prf
faFaIff k vs ws f = 
  let (k', vxs) = varPars k vs in
  let ksks' = rangeOver k (vs ++ ws) in
  let ks = rangeOver k vs in
  let ks' = rangeOver k' ws in
  let (_, wxs) = varPars k' ws in
  let f' = substForm vxs f in
  let f'' = substForm wxs f' in
  iffRFull (Fa vs (Fa ws f)) (Fa (vs ++ ws) f) 
    (FaF' (vs ++ ws) ksks' f $ FaT' vxs (Fa ws f) $ FaT' wxs f' $ Id' f'') 
    (FaF' vs ks (Fa ws f) $ FaF' ws ks' f' $ FaT' (vxs ++ wxs) f $ Id' f'')

-- exExIff k vs ws f : |- ? vs (? ws f) <=> ? (vs ++ ws) f
exExIff :: Int -> [BS] -> [BS] -> Form -> Prf
exExIff k vs ws f = 
  let (k', vxs) = varPars k vs in
  let vks = rangeOver k vs in
  let wks = rangeOver k' ws in
  let vwks = rangeOver k (vs ++ ws) in
  let (_, wxs) = varPars k' ws in
  let f' = substForm vxs f in
  let f'' = substForm wxs f' in
  iffRFull (Ex vs (Ex ws f)) (Ex (vs ++ ws) f) 
    (ExT' vs vks (Ex ws f) $ ExT' ws wks f' $ ExF' (vxs ++ wxs) f $ Id' f'')
    (ExT' (vs ++ ws) vwks f $ ExF' vxs (Ex ws f) $ ExF' wxs f' $ Id' f'') 
    
faIffToFaIffFa :: [BS] -> Int -> Form -> Form -> Prf
faIffToFaIffFa vs k f g = 
  let (_, vxs) = varPars k vs in
  let f' = substForm vxs f in
  let g' = substForm vxs g in
  IffF' (Fa vs f) (Fa vs g) 
    (faImpFa vs k f g $ FaT' vxs (f <=> g) $ iffMP f' g') 
    (faImpFa vs k g f $ FaT' vxs (f <=> g) $ iffMPR f' g')

-- ! vs (f <=> g) |- (? vs f) <=> (? vs g)
faIffToExIffEx :: [BS] -> Int -> Form -> Form -> Prf
faIffToExIffEx vs k f g = 
  let (_, vxs) = varPars k vs in
  let f' = substForm vxs f in
  let g' = substForm vxs g in
  IffF' (Ex vs f) (Ex vs g) 
    (exImpEx vs k f g $ FaT' vxs (f <=> g) $ iffMP f' g') 
    (exImpEx vs k g f $ FaT' vxs (f <=> g) $ iffMPR f' g')

congAux :: [(Term, Term)] -> Prf -> Prf
congAux [] = id
congAux ((x, y) : xys) = Cut'(y === x) (EqS' x y) . congAux xys 

-- eqCong w x y z : w = x, x = y, y = z |- w = z
eqTrans2 :: Term -> Term -> Term -> Term -> Prf
eqTrans2 w x y z = Cut'(x === z) (EqT' x y z) (EqT' w x z)

iffRFull :: Form -> Form -> Prf -> Prf -> Prf
iffRFull f g po pr = IffF' f g (impFAC f g po) (impFAC g f pr)

-- relCong r xs ys : x0 = y0 ... xn = yn |- r(x0 ... xn) <=> r(y0 ... yn)
relCong :: Funct -> [Term] -> [Term] -> IO Prf
relCong r xs ys = do 
  xys <- zipM xs ys 
  return $ congAux xys $ iffRFull (Rel r xs) (Rel r ys) (RelC' r xs ys) (RelC' r ys xs)

notTF :: Form -> Form -> Prf -> Prf
notTF f g p = NotT' f $ NotF' g p

-- iffNotNot f : |- f <=> ~~f
iffNotNot :: Form -> Prf
iffNotNot f =
  iffRFull f (Not (Not f))
    (NotF' (Not f) $ NotT' f $ Id' f)
    (NotT' (Not f) $ NotF' f $ Id' f)

-- notNotIff f : |- ~~f <=> f
notNotIff :: Form -> Prf
notNotIff f =
  iffRFull (Not (Not f)) f
    (NotT' (Not f) $ NotF' f $ Id' f)
    (NotF' (Not f) $ NotT' f $ Id' f)

rDefLemma0 :: Form -> Form -> Prf
rDefLemma0 f g =
  let p = IffTO' f g (mp f g) in -- f, f <=> g |- g
  OrF' [g, Not f] [g, Not f] $ NotF' f p -- f <=> g |- g \/ ~f

rDefLemma1 :: Form -> [Form] -> [Form] -> Prf
rDefLemma1 r fs fsnr =
  let pl = rDefLemma0 r (Or fs) in -- (r <=> \/ fs) |- (\/ fs) \/ ~r
  let ps = map (\ f_ -> (f_, Id' f_)) fs in
  let pfsnr = OrT' [(Or fs, OrT' ps), (Not r, Id' (Not r))] in -- pfsnr : (\/ fs) \/ ~r |- fs, ~r
  let pr = OrF' fsnr fsnr pfsnr in                           -- ps    : (\/ fs) \/ ~r |- \/ fsnr
  Cut'(Or [Or fs, Not r]) pl pr -- (r <=> \/ fs) |- \/ fsnr

-- notIffIffAnd f g : |- ~(f <=> g) <=> ((~g \/ ~f) /\ (g \/ f))
notIffIffAnd :: Form -> Form -> Prf
notIffIffAnd f g = 
  let rhs = [Or [Not g, Not f], Or [g, f]] in
  let _p1 = IffF' f g (ImpFC' f g $ Id' g) (ImpFC' g f $ Id' f) in -- _p1 : f, g |- f <=> g
  let p1 = OrF' [Not g, Not f] [Not g, Not f] $ NotF' g $ NotF' f _p1 in -- p1 : |- f <=> g, (~g \/ ~f)
  let p2 = OrF' [g, f] [g, f] $ IffF' f g (ImpFA' f g $ Id' f) (ImpFA' g f $ Id' g) in -- p2 : |- f <=> g, (g \/ f)
  let p3 = OrT' [(g, Id' g), (f, iffMP f g)] in -- p3 : f <=> g, (g \/ f) |- g
  let p4 = OrT' [(g, iffMPR f g), (f, Id' f)] in -- p4 : f <=> g, (g \/ f) |- f
  iffRFull (Not (Iff f g)) (And rhs)
    (NotT' (f <=> g) $ AndF' [(Or [Not g, Not f], p1), (Or [g, f], p2)])
    (NotF' (f <=> g) $ AndT' rhs rhs $ OrT' [(Not g, NotT' g p3), (Not f, NotT' f p4)]) 

singleOrIff :: Form -> Prf
singleOrIff f = iffRFull (Or [f]) f (OrT' [(f, Id' f)]) (OrF' [f] [f] $ Id' f)

singleAndIff :: Form -> Prf
singleAndIff f = iffRFull (And [f]) f (AndT' [f] [f] $ Id' f) (AndF' [(f, Id' f)])

-- faTopIff : Fa vs Top <=> Top
faTopIff :: Int -> [BS] -> Prf
faTopIff k vs = 
  let ks = rangeOver k vs in
  iffRFull (Fa vs Top) Top TopF' (FaF' vs ks Top TopF')

-- faBotIff : Fa vs Top <=> Top
faBotIff :: [BS] -> Prf
faBotIff vs = 
  let vxs = map (, zt) vs in
  iffRFull (Fa vs Bot) Bot (FaT' vxs Bot BotT') BotT'

-- exBotIff : Ex vs Bot <=> Bot
exBotIff :: Int -> [BS] -> Prf
exBotIff k vs =
  let ks = rangeOver k vs in
  iffRFull (Ex vs Bot) Bot (ExT' vs ks Bot BotT') BotT'

-- exTopIff : Ex vs Top <=> Top
exTopIff :: [BS] -> Prf
exTopIff vs = 
  let vxs = map (, zt) vs in
  iffRFull (Ex vs Top) Top TopF' (ExF' vxs Top TopF')

-- degenOrIff fs : \/ fs <=> Top
-- requires : Top <- fs
degenOrIff :: [Form] -> Prf
degenOrIff fs = iffRFull (Or fs) Top TopF' (OrF' fs [Top] TopF')

-- degenAndIff fs : /\ fs <=> Bot
-- requires : Bot <- fs
degenAndIff :: [Form] -> Prf
degenAndIff fs = iffRFull (And fs) Bot (AndT' fs [Bot] BotT') BotT'

-- bloatOrIff fs : \/ fs <=> \/ (fs \ {Bot})
bloatOrIff :: [Form] -> Prf
bloatOrIff fs = 
  let gs = filter (not . isBot) fs in 
  let fps = 
        map 
          ( \ f_ -> 
             case f_ of 
               Bot -> (f_, BotT')
               _ -> (f_, Id' f_ ) )
          fs in
  let gps = map (\ g_ -> (g_, Id' g_)) gs in
  iffRFull (Or fs) (Or gs) (OrF' gs gs $ OrT' fps) (OrF' fs fs $ OrT' gps)

-- requires : (fs \ {Bot}) = {f}
-- bloatOrIff' fs f : \/ fs <=> f
bloatOrIff' :: [Form] -> Form -> Prf
bloatOrIff' fs f = 
  let fps = map (\ f_ -> if isBot f_ then (f_, BotT') else (f_, Id' f_)) fs in
  iffRFull (Or fs) f (OrT' fps) (OrF' fs [f] $ Id' f)

-- requires : (fs \ {Top}) = {f}
-- bloatAndIff' fs f : /\ fs <=> f
bloatAndIff' :: [Form] -> Form -> Prf
bloatAndIff' fs f = 
  let fps = map (\ f_ -> if isTop f_ then (f_, TopF') else (f_, Id' f_)) fs in
  iffRFull (And fs) f (AndT' fs [f] $ Id' f) (AndF' fps)

-- bloatAndIff fs : /\ fs <=> /\ (fs \ {Top})
bloatAndIff :: [Form] -> Prf
bloatAndIff fs = 
  let gs = filter (not . isTop) fs in 
  let fps = 
        map 
          ( \ f_ -> 
             case f_ of 
               Top -> (f_, TopF')
               _ -> (f_, Id' f_ ) )
          fs in
  let gps = map (\ g_ -> (g_, Id' g_)) gs in
  iffRFull (And fs) (And gs) (AndT' fs fs $ AndF' gps) (AndT' gs gs $ AndF' fps)