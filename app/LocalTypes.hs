{-# LANGUAGE OverloadedStrings #-}

module LocalTypes where

import Types
import Basic
import Parse
import PP
import Data.List as L 
import Data.Map as HM
import Data.Set as S (Set, toList, insert, member)
import qualified Data.ByteString as BS
import Control.Monad as M (guard, MonadPlus(mzero))
import Data.Maybe (fromMaybe, fromJust)
import Data.ByteString.Builder (Builder)
import Control.Applicative ((<|>))

data Stelab =
    InfStep Form Prf BS
  | DefStep Form Form Prf BS
  | AoCStep [Term] Form Form Prf BS
  deriving (Show)

data Prf =
    Id' Form
  | EqR' Term
  | EqS' Term Term
  | EqT' Term Term Term
  | FunC' Funct [Term] [Term]
  | RelC' Funct [Term] [Term]
  | BotT' 
  | TopF' 
  | NotT' Form Prf
  | NotF' Form Prf
  | OrT' [(Form, Prf)]
  | OrF' [Form] [Form] Prf
  | AndT' [Form] [Form] Prf
  | AndF' [(Form, Prf)]
  | ImpT' Form Form Prf Prf
  | ImpFA' Form Form Prf
  | ImpFC' Form Form Prf
  | IffTO' Form Form Prf
  | IffTR' Form Form Prf
  | IffF' Form Form Prf Prf
  | FaT' [(BS, Term)] Form Prf
  | FaF' [BS] [Int] Form Prf
  | ExT' [BS] [Int] Form Prf
  | ExF' [(BS, Term)] Form Prf
  | Cut' Form Prf Prf 
  | Mrk BS Prf 
  | Open'
  deriving (Show)

cuts :: [(Form, Prf)] -> Prf -> Prf
cuts [] prf = prf
cuts ((f, p0) : fps) p1 = Cut' f p0 (cuts fps p1) 

ppPrf :: Int -> Prf -> Builder
ppPrf k p = ppInter "\n" $ ppPrfCore k p

fromJust' :: String -> Maybe a -> a
fromJust' s Nothing = error s
fromJust' _ (Just x) = x

ppPrfCore :: Int -> Prf -> [Builder]
ppPrfCore 0 _ = ["..."]
ppPrfCore k (Id' f) = ["Id' : " <> ppForm f]
ppPrfCore k (NotT' f p) = ("Not-L : " <> ppForm (Not f)) : L.map pad (ppPrfCore (k - 1) p)
ppPrfCore k (NotF' f p) = ("Not-R : " <> ppForm (Not f)) : L.map pad (ppPrfCore (k - 1) p)
ppPrfCore k (Cut' f p0 p1) = ("Cut : " <> ppForm f) : L.map pad (ppPrfCore (k - 1) p0 ++ ppPrfCore (k - 1) p1)
ppPrfCore k (IffF' f g p0 p1) = ("Iff-R : " <> ppForm (f <=> g)) : L.map pad (ppPrfCore (k - 1) p0 ++ ppPrfCore (k - 1) p1)
ppPrfCore k (IffTO' f g p) = ("Iff-LO : " <> ppForm (f <=> g)) : L.map pad (ppPrfCore (k - 1) p)
ppPrfCore k (IffTR' f g p) = ("Iff-LR : " <> ppForm (f <=> g)) : L.map pad (ppPrfCore (k - 1) p)
ppPrfCore k (ImpT' f g p0 p1) = ("Imp-L : " <> ppForm (f ==> g)) : L.map pad (ppPrfCore (k - 1) p0 ++ ppPrfCore (k - 1) p1)
ppPrfCore k (ImpFC' f g p) = ("Imp-RC : " <> ppForm (f ==> g)) : L.map pad (ppPrfCore (k - 1) p)
ppPrfCore k (ImpFA' f g p) = ("Imp-RA : " <> ppForm (f ==> g)) : L.map pad (ppPrfCore (k - 1) p)
ppPrfCore k (Mrk s p) = ("Mark : " <> ft s) : L.map pad (ppPrfCore (k - 1) p)
ppPrfCore k (FunC' f xs ys) = ["Fun-C : ", "  f : " <> ppFunct f, "  xs : " <> ppList ppTerm xs, "  ys : " <> ppList ppTerm ys]
ppPrfCore k (RelC' r xs ys) = ["Rel-C : ", "  r : " <> ppFunct r, "  xs : " <> ppList ppTerm xs, "  ys : " <> ppList ppTerm ys]
ppPrfCore k (OrT' fps) = "Or-L" : L.map pad (L.concatMap (\ (f_, p_) -> ": " <> ppForm f_ : ppPrfCore (k - 1) p_) fps)
ppPrfCore k (OrF' fs fs' p) = ("Or-R : " <> ppForm (Or fs)) : L.map pad (ppPrfCore (k - 1) p)
ppPrfCore k (AndT' fs fs' p) = ("And-L : " <> ppForm (And fs)) : L.map pad (ppPrfCore (k - 1) p)
ppPrfCore k (AndF' fps) = "And-R" : L.map pad (L.concatMap (\ (f_, p_) -> ": " <> ppForm f_ : ppPrfCore (k - 1) p_) fps)
ppPrfCore k (EqS' x y) = ["Eq-S?"]
ppPrfCore k (EqR' x) = ["Eq-R : " <> ppTerm x]
ppPrfCore k (EqT' x y z) = ["Eq-T?"]
ppPrfCore k (FaT' vxs f p) =
  let (vs, xs) = unzip vxs in
  ("Fa-L : " : L.map (pad . ppMapping) vxs) ++ pad (ppForm (Fa vs f)) : L.map pad (ppPrfCore (k - 1) p)
ppPrfCore k (ExF' vxs f p) =
  let (vs, xs) = unzip vxs in
  ("Ex-R : " : L.map (pad . ppMapping) vxs) ++ pad (ppForm (Ex vs f)) : L.map pad (ppPrfCore (k - 1) p)
ppPrfCore k (FaF' vs ms f p) =
  -- let (_, vxs) = varPars m vs in
  let vxs = fromJust' ("faf-case :\n" ++ bd2str (ppList ft vs) ++ "\n" ++ bd2str (ppList ppInt ms)) (zipM vs $ L.map par ms) in
  ("Fa-R : " : L.map (pad . ppMapping) vxs) ++ pad (ppForm (Fa vs f)) : L.map pad (ppPrfCore (k - 1) p)
ppPrfCore k (ExT' vs ms f p) =
  let vxs = fromJust' "ext-case" (zipM vs $ L.map par ms) in
  ("Ex-L : " : L.map (pad . ppMapping) vxs) ++  pad (ppForm (Ex vs f)) : L.map pad (ppPrfCore (k - 1) p)
ppPrfCore k Open' = ["Open!"]
ppPrfCore k BotT' = ["Bot-T"]
ppPrfCore k TopF' = ["Top-F"]

-- ppStelab :: Stelab -> Builder
-- ppStelab (InfStep f p t) = ppInter "\n" $ ["InfStep", "f :" <> ppForm f, "prf :"] ++ ppPrfCore 20 p ++ ["Notes : " <> ft t]
-- ppStelab (DefStep f g _ t) = "rdef : " <> ppForm f <> " |- " <> ppForm g <> "\nNotes : " <> ft t
-- ppStelab (AoCStep xs _ _ _ t) = "AoC :\nxs : " <> ppListNl ppTerm xs <> "\nNotes : " <> ft t

prfHasAsm :: Prf -> Bool
prfHasAsm (Id' _) = False
prfHasAsm TopF' = False
prfHasAsm BotT' = False
prfHasAsm (EqR' _) = False
prfHasAsm (EqS' _ _) = False
prfHasAsm EqT'  {} = False
prfHasAsm FunC' {} = False
prfHasAsm RelC' {} = False
prfHasAsm (Cut' f p0 p1) = prfHasAsm p0 || prfHasAsm p1
prfHasAsm (ImpFA' _ _ p) = prfHasAsm p
prfHasAsm (ImpFC' _ _ p) = prfHasAsm p
prfHasAsm (IffTO' _ _ p) = prfHasAsm p
prfHasAsm (IffTR' _ _ p) = prfHasAsm p
prfHasAsm (ImpT' _ _ p0 p1) = prfHasAsm p0 || prfHasAsm p1
prfHasAsm (IffF' _ _ p0 p1) = prfHasAsm p0 || prfHasAsm p1
prfHasAsm (OrT' fps) = L.any (prfHasAsm . snd) fps
prfHasAsm (AndF' fps) = L.any (prfHasAsm . snd) fps
prfHasAsm (OrF' _ _ p) = prfHasAsm p
prfHasAsm (AndT' _ _ p) = prfHasAsm p
prfHasAsm (NotT' _ p) = prfHasAsm p
prfHasAsm (NotF' _ p) = prfHasAsm p
prfHasAsm (FaT' _ _ p) = prfHasAsm p
prfHasAsm (FaF' _ _ _ p) = prfHasAsm p
prfHasAsm (ExT' _ _ _ p) = prfHasAsm p
prfHasAsm (ExF' _ _ p) = prfHasAsm p
prfHasAsm (Mrk _ p) = prfHasAsm p
prfHasAsm Open' = True

data Dir = 
  Obv | Rev
  deriving (Show, Eq, Ord)

data Lrat = Del Int [Int] | Add Int [Form] [Int]
  deriving (Show)

type VC = (HM.Map BS (Set BS), HM.Map BS (Set BS)) 
type VR = (HM.Map BS BS, HM.Map BS BS) 
type VM = HM.Map BS Term

data Path =
    NewRel Funct Int
  | NewFun Funct Int
  | NewEq
  | NewFa Bool
  | NewEx Bool
  | NewImpL
  | NewImpR
  | NewIffL
  | NewIffR
  | NewOr Int Int
  | NewAnd Int Int
  | NewNot
  deriving (Ord, Eq)

data PrePath =
    PreRel Funct Int
  | PreFun Funct Int
  | PreEq
  | PreFa [BS]
  | PreEx [BS]
  | PreImpL
  | PreImpR
  | PreIffL
  | PreIffR
  | PreOr Int Int
  | PreAnd Int Int
  | PreNot
  deriving (Ord, Eq)

type Sig = HM.Map [Path] Int
type Sigs = HM.Map BS Sig

type RSTA = (VM, Maybe (Form, Dir), [Form], [Form], [Form])
type SST = (VM, [Form], [Form], [(Term, Term)])
type EFS = (VM, Maybe Bool, [Form])
type FSTA = (VM, [Form])
type EQFS = (VM, [Form], [(Term, Term)])
type MTT = HM.Map BS BS
type MTI = HM.Map BS Int
type USOL = [Term]

type Step = (BS, BS, [BS], Form) -- (name, inference, hyps, conc)

type Nodes = HM.Map BS (Form, Bool, Int)


agvmt :: VM -> Term -> Term
agvmt gm (Var v) =
  case HM.lookup v gm of
    Just x -> gndTerm x
    _ -> zt
agvmt gm (Fun f xs) = Fun f $ L.map (agvmt gm) xs

avmt :: VM -> Term -> Term
avmt gm (Var v) =
  case HM.lookup v gm of
    Just x -> x
    _ -> Var v
avmt gm (Fun f xs) = Fun f $ L.map (avmt gm) xs

tavmt :: VM -> Term -> Maybe Term
tavmt gm (Var v) =
  case HM.lookup v gm of
    Just x -> return x
    _ -> mzero -- return $ Var v
tavmt gm (Fun f xs) = Fun f <$> mapM (tavmt gm) xs

tavmf :: VM -> Form -> Maybe Form
tavmf _ Top = Just Top
tavmf _ Bot = Just Bot
tavmf gm (Eq x y) = do
  x' <- tavmt gm x
  y' <- tavmt gm y
  return (Eq x' y')
tavmf gm (Rel r xs) = Rel r <$> mapM (tavmt gm) xs
tavmf gm (Or fs) = Or <$> mapM (tavmf gm) fs
tavmf gm (And fs) = And <$> mapM (tavmf gm) fs
tavmf gm (Not f) = do
  f' <- tavmf gm f
  return (Not f')
tavmf gm (Imp f g) = do
  f' <- tavmf gm f
  g' <- tavmf gm g
  return (Imp f' g')
tavmf gm (Iff f g) = do
  f' <- tavmf gm f
  g' <- tavmf gm g
  return (Iff f' g')
tavmf gm (Fa vs f) = Fa vs <$> tavmf gm f
tavmf gm (Ex vs f) = Ex vs <$> tavmf gm f

getShortList :: [[a]] -> Maybe [a]
getShortList [] = nt
getShortList [xs] = return xs
getShortList ([] : xss) = return []
getShortList ([x] : xss) = return [x]
getShortList (xs : xss) = do
  ys <- getShortList xss
  if shorter xs ys
  then return xs
  else return ys

shorter :: [a] -> [b] -> Bool
shorter _ [] = False
shorter [] _ = True
shorter (_ : xs) (_ : ys) = shorter xs ys

appVrTerm :: VR -> Term -> Term
appVrTerm vr (Var v) =
  case HM.lookup v (fst vr) of
    Just x -> Var x
    _ -> error "appVrTerm : no mapping"
appVrTerm vw (Fun f xs) = Fun f $ L.map (appVrTerm vw) xs

appVrForm :: VR -> Form -> Form
appVrForm _ Top = Top
appVrForm _ Bot = Bot
appVrForm vr (Not f) = Not $ appVrForm vr f
appVrForm vr (Fa vs f) = Fa (L.map (\ v_ -> HM.findWithDefault "_" v_ (fst vr)) vs) $ appVrForm vr f
appVrForm vr (Ex vs f) = Ex (L.map (\ v_ -> HM.findWithDefault "_" v_ (fst vr)) vs) $ appVrForm vr f
appVrForm vr (Imp f g) = Imp (appVrForm vr f) (appVrForm vr g)
appVrForm vr (Iff f g) = Iff (appVrForm vr f) (appVrForm vr g)
appVrForm vr (Or fs) = Or $ L.map (appVrForm vr) fs
appVrForm vr (And fs) = And $ L.map (appVrForm vr) fs
appVrForm vr (Rel r xs) = Rel r $ L.map (appVrTerm vr) xs
appVrForm vr (Eq x y) = Eq (appVrTerm vr x) (appVrTerm vr y)

pairWithVR' :: VR -> BS -> IO (BS, Term)
pairWithVR' (vw, _) v = 
  case HM.lookup v vw of 
    Just w -> return (v, Var w)
    _ -> mzero

pairWithVR :: VR -> [(BS, Term)] -> BS -> Term
pairWithVR (vw, _) wxs v =
  fromMaybe zt ( do w <- HM.lookup v vw
                    snd <$> L.find ((w ==) . fst) wxs )

formSJ :: Form -> Bool
formSJ (Or [_])  = True
formSJ (And [_]) = True
formSJ (Not f) = formSJ f
formSJ (Imp f g) = formSJ f || formSJ g
formSJ (Iff f g) = formSJ f || formSJ g
formSJ (Or fs) = L.any formSJ fs
formSJ (And fs) = L.any formSJ fs
formSJ (Fa _ f) = formSJ f
formSJ (Ex _ f) = formSJ f
formSJ _ = False

-- elabSingleJunct :: Elab -> Bool
-- elabSingleJunct ((_, _, f), _, _) = formSJ f

gentToText :: Gent -> Maybe BS
gentToText (GenT t []) = return t
gentToText _ = Nothing

anfToStep :: Anf -> Maybe Step
anfToStep (n, r, g, Just (GenT "file" [_, GenT m []], _)) = return (n, "file", [m], conjecturize r g)
anfToStep (n, _, g, Just (GenT "introduced" [GenT "predicate_definition_introduction" [],
  Genl [GenT "new_symbols" [GenT "naming" [],Genl [GenT r []]]]], _)) =
    return (n, "predicate_definition_introduction", [], g)
anfToStep (n, _, g, Just (GenT "introduced" [GenT "avatar_definition" [],
  Genl [GenT "new_symbols" [GenT "naming" [], Genl [GenT r []]]]], _)) =
    return (n, "avatar_definition", [], g)
anfToStep (n, _, g, Just (GenT "introduced" [GenT "choice_axiom" [], Genl []], _)) =
  return (n, "choice_axiom", [], g)
anfToStep (n, _, g, Just (GenT "inference" [GenT "avatar_sat_refutation" [], _, Genl l], _)) = do
  txs <- mapM gentToText l
  return (n, "avatar_sat_refutation", txs, g)
anfToStep (n, _, g, Just (GenT "inference" [GenT r [], _, Genl l], _)) = do
  txs <- mapM gentToText l
  return (n, r, txs, g)
anfToStep (_, _, _, Just (ft, _)) = error $ "AF-to-step failure (Just) : " ++ show (ppGent ft) ++ "\n"
anfToStep (_, _, _, Nothing) = error "AF-to-step failure (Nothing)"

sortSteps :: [Step] -> [Step]
sortSteps = sortBy compareSteps

compareSteps :: Step -> Step -> Ordering
compareSteps (m :> ms, _, _, _) (n :> ns, _, _, _) =
  case compare m n of
    EQ ->
      case (bs2int ms, bs2int ns) of
        (Just i, Just j) -> compare i j
        _ -> error "Cannot compare step names"
    other -> other
compareSteps _ _ = LT

ppStep :: Step -> Builder
ppStep (n, r, ns, f) =
  ft n <> " :: " <>
  ft r <> " :: " <>
  ppList ft ns <> " :: " <>
  ppForm f <> "\n"

ppPath :: Path -> Builder
ppPath (NewRel _ _) = "rel"
ppPath (NewFun _ _) = "fun"
ppPath NewEq = "eq"
ppPath (NewFa _) = "fa"
ppPath (NewEx _) = "ex"
ppPath NewImpL = "imp-l"
ppPath NewImpR = "imp-r"
ppPath NewIffL = "iff-l"
ppPath NewIffR = "iff-r"
ppPath (NewOr _ _) = "or"
ppPath (NewAnd _ _) = "and"
ppPath NewNot = "not"

ppSig :: Sig -> Builder
ppSig = ppHM (ppList ppPath) ppInt

ppLrat :: Lrat -> Builder
ppLrat (Del k ks) = ppInt k  <> ". Del " <> ppInter " " (L.map ppInt ks)
ppLrat (Add k fs ms) = ppInt k  <> ". Add " <> ppInter " " (L.map ppForm fs) <> ", Using : " <> ppInter  " " (L.map ppInt ms)

ppMapping :: (BS, Term) -> Builder
ppMapping (t, x) = ft t <> " |-> " <> ppTerm x

ppVmap :: (BS, BS) -> Builder
ppVmap (v, w) = ft $  v <> " <-|-> " <> w

ppVR :: VR -> Builder
ppVR (vw, _) = ppListNl ppVmap (HM.toList vw)

ppVCAux :: HM.Map BS (Set BS) -> Builder
ppVCAux vw = ppListNl (\ (v_, ws_) -> ft v_ <> " |-> " <> ppList ft (S.toList ws_)) (HM.toList vw)

ppVC :: VC -> Builder
ppVC (vws, wvs) = ppVCAux vws <> "-------------------------------------\n" <> ppVCAux wvs

type Invranch = HM.Map (Bool, Form) BS

{- Verification -}

isRelD :: Form -> Bool
isRelD (Fa vs (Iff (Rel s xs) f)) = L.map Var vs == xs && isGndForm vs f
isRelD (Iff (Rel s []) f) = isGndForm [] f
isRelD _ = False

verifyEqGoal :: Int -> Set Form -> Set Form -> (Term, Term, Prf) -> IO ()
verifyEqGoal k lft rgt (x, y, p) = verify k lft (S.insert (Eq x y) rgt) p

verifyRgtGoal :: Int -> Set Form -> Set Form -> (Form, Prf) -> IO ()
verifyRgtGoal k lft rgt (f, p) = verify k lft (S.insert f rgt) p

verifyLftGoal :: Int -> Set Form -> Set Form -> (Form, Prf) -> IO ()
verifyLftGoal k lft rgt (f, p) = verify k (S.insert f lft) rgt p

ev :: BS -> Form -> Set Form -> Set Form -> IO ()
ev t f lhs rhs = error $ bd2str $ ft t <> ppForm f <> "\nLHS :\n" <> ppListNl (ppNL ppForm) (S.toList lhs) <> "\nRHS :\n" <> ppListNl (ppNL ppForm) (S.toList rhs) <> "\n"

eb :: Builder -> a
eb bd = error (bd2str bd)

verify :: Int -> Set Form -> Set Form -> Prf -> IO ()
verify _ _ _ Open' = return ()
verify _ lft rgt BotT' = guard $ S.member Bot lft
verify _ lft rgt TopF' = guard $ S.member Top rgt
verify _ lft rgt (Id' f) = do
  let lhs_text = ppListNl ppForm (S.toList lft)
  let rhs_text = ppListNl ppForm (S.toList rgt)
  guard (S.member f lft) <|> error (bd2str $ "Id' fail, LHS missing : " <> ppForm f <> "\nLHS = " <> lhs_text)
  guard (S.member f rgt) <|> error (bd2str $ "Id' fail, RHS missing : " <> ppForm f <> "\nRHS = " <> rhs_text)
verify _ lft rgt (EqR' x) = guard (S.member (Eq x x) rgt) <|> error "EqR'-fail"
verify k lft rgt (EqS' x y) =
  guard (S.member (Eq x y) lft && S.member (Eq y x) rgt) <|> error "EqS'-fail"
verify k lft rgt (EqT' x y z) =
  guard (S.member (Eq x y) lft && S.member (Eq y z) lft && S.member (Eq x z) rgt) <|> error "EqT'-fail"
verify k lft rgt (FunC' f xs ys) = do
  xys <- zipM xs ys
  guardMsg "Fun-C : premise missing" $ L.all (\ (x_, y_) -> S.member (x_ === y_) lft) xys
  guardMsg "Fun-C : conclusion missing" $ S.member (Fun f xs === Fun f ys) rgt
verify k lft rgt (RelC' r xs ys) = do
  xys <- zipM xs ys
  guardMsg "Fun-C : eq-premise missing" $ L.all (\ (x_, y_) -> S.member (x_ === y_) lft) xys
  guardMsg "Fun-C : premise missing" $ S.member (Rel r xs) lft
  guardMsg "Fun-C : conclusion missing" $ S.member (Rel r ys) rgt
verify k lft rgt (NotT' f p) = do
  guard (S.member (Not f) lft) <|> error "NotT'-fail"
  verify k lft (S.insert f rgt) p
verify k lft rgt (NotF' f p) = do
  guard (S.member (Not f) rgt) <|> eb ("NotF'-fail\nCannot find hyp : " <> ppSignForm (False, Not f) <> "\nFrom :\n" <> ppSetNl ppForm rgt)
  verify k (S.insert f lft) rgt p
verify k lft rgt (OrT' gls) = do
  let fs = L.map fst gls
  guard (S.member (Or fs) lft) <|> eb ("OrT'-fail : " <> ppForm (Or fs))
  mapM_ (verifyLftGoal k lft rgt) gls
verify k lft rgt (OrF' fs gs p) = do
  guard (sublist gs fs && S.member (Or fs) rgt) <|> error "OrF'-fail"
  verify k lft (L.foldl (flip S.insert) rgt gs) p
verify k lft rgt (AndT' fs gs p) = do
  guard (sublist gs fs) <|> error "AndT'-fail : not subset"
  guard (S.member (And fs) lft) <|> ev "AndT'-fail : " (And fs) lft rgt
  verify k (L.foldl (flip S.insert) lft gs) rgt p
verify k lft rgt (AndF' gls) = do
  let fs = L.map fst gls
  guard (S.member (And fs) rgt) <|> ev "AndF'-fail" (And fs) lft rgt
  mapM_ (verifyRgtGoal k lft rgt) gls
verify k lft rgt (ImpT' f g p q) = do
  guard (S.member (Imp f g) lft) <|> ev "ImpT'-fail" (f ==> g) lft rgt
  verify k lft (S.insert f rgt) p
  verify k (S.insert g lft) rgt q
verify k lft rgt (ImpFA' f g p) = do
  guard (S.member (Imp f g) rgt) <|> error "ImpFA'-fail"
  verify k (S.insert f lft) rgt p
verify k lft rgt (ImpFC' f g p) = do
  guard (S.member (Imp f g) rgt) <|> error "ImpFC'-fail"
  verify k lft (S.insert g rgt) p
verify k lft rgt (IffF' f g p q) = do
  guard (S.member (Iff f g) rgt) <|> ev "IffF'-fail" (f <=> g) lft rgt
  verify k lft (S.insert (Imp f g) rgt) p
  verify k lft (S.insert (Imp g f) rgt) q
verify k lft rgt (IffTO' f g p) = do
  guard (S.member (Iff f g) lft) <|> ev "IffTO'-fail : " (f <=> g) lft rgt
  verify k (S.insert (Imp f g) lft) rgt p
verify k lft rgt (IffTR' f g p) = do
  guard (S.member (f <=> g) lft) <|> ev "IffTR'-fail : " (f <=> g) lft rgt
  verify k (S.insert (Imp g f) lft) rgt p
verify k lft rgt (FaT' vxs f p) = do
  let vs = L.map fst vxs
  guard (S.member (Fa vs f) lft) <|> ev "FaT'-fail : " (Fa vs f) lft rgt
  verify k (S.insert (substForm vxs f) lft) rgt p
verify k lft rgt (FaF' vs ms f p) = do
  let xs = L.map par ms
  guard $ L.all (k <=) ms
  guard $ not $ hasDup ms
  vxs <- zipM vs xs <|> error "FaF'-fail : cannot zip"
  f' <- substitute vs xs f
  verify (maximum ms + 1) lft (S.insert f' rgt) p
verify k lft rgt (ExT' vs ms f p) = do
  let xs = L.map par ms
  guard $ L.all (k <=) ms
  guard $ not $ hasDup ms
  vxs <- zipM vs xs <|> error "ExT'-fail : cannot zip"
  f' <- substitute vs xs f
  verify (maximum ms + 1) (S.insert f' lft) rgt p
verify k lft rgt (ExF' vxs f p) = do
  let vs = L.map fst vxs
  guard (S.member (Ex vs f) rgt) <|> error "ExF'-fail"
  verify k lft (S.insert (substForm vxs f) rgt) p
verify k lft rgt (Cut' f p0 p1) = do
  verify k lft (S.insert f rgt) p0
  verify k (S.insert f lft) rgt p1
verify k lft rgt (Mrk s p) = verify k lft rgt p

