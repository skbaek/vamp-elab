module Norm where 

import Types
import Basic

import Data.Set as S ( Set, member )

import Data.List as L

boolSimp :: Form -> Form
boolSimp (Rel r xs) = Rel r xs
boolSimp (Eq x y) = Eq x y
boolSimp Top = Top
boolSimp Bot = Bot
boolSimp (Not f) =
  case boolSimp f of
    Top -> Bot
    Bot -> Top
    g -> Not g
boolSimp (Or fs) =
  let gs = L.map boolSimp fs in
  if Top `elem` gs 
    then Top
    else Or $ L.filter (/= Bot) gs 
boolSimp (And fs) =
  let gs = L.map boolSimp fs in
  if Bot `elem` gs 
    then Bot
    -- else case L.filter (/= Top) gs of
    --        [g] -> g
    --        hs -> And hs
    else And $ L.filter (/= Top) gs 
boolSimp (Fa vs f) =
  case boolSimp f of
    Top -> Top
    Bot -> Bot
    g -> Fa vs g
boolSimp (Ex vs f) =
  case boolSimp f of
    Top -> Top
    Bot -> Bot
    g -> Ex vs g
boolSimp (Imp f g) =
  case (boolSimp f, boolSimp g) of
    (Bot, _) -> Top
    (_, Top) -> Top
    (Top, g_) -> g_
    (f_, Bot) -> Not f_
    (f', g') -> Imp f' g'
boolSimp (Iff f g) =
  case (boolSimp f, boolSimp g) of
    (Top, g') -> g'
    (f', Top) -> f'
    (Bot, g') -> Not g'
    (f', Bot) -> Not f'
    (f', g') -> Iff f' g'

flatOr :: [Form] -> [Form]
flatOr [] = error "Cannot flatten empty disjunction"
flatOr [Or fs] = flatOr fs
flatOr [f] = [f]
flatOr (Bot : fs) = flatOr fs
flatOr (Or fs : gs) = flatOr fs ++ flatOr gs
flatOr (f : fs) = f : flatOr fs

flatAnd :: [Form] ->[Form]
flatAnd [] = error "Cannot flatten empty conjunction"
flatAnd [And fs] = flatAnd fs
flatAnd [f] = [f]
flatAnd (Top : fs) = flatAnd fs
flatAnd (And fs : gs) = flatAnd fs ++ flatAnd gs
flatAnd (f : fs) = f : flatAnd fs

dne :: Form -> Form
dne (Not (Not f)) = dne f
dne (Not f) = Not $ dne f
dne (Or fs) = Or $ L.map dne fs
dne (And fs) = And $ L.map dne fs
dne (Imp f g) = Imp (dne f) (dne g)
dne (Iff f g) = Iff (dne f) (dne g)
dne (Fa vs f) = Fa vs $ dne f
dne (Ex vs f) = Ex vs $ dne f
dne f = f

qmerge :: Form -> Form
qmerge (Not f) = Not $ qmerge f
qmerge (Or fs)  = Or $ L.map qmerge fs
qmerge (And fs) = And $ L.map qmerge fs
qmerge (Imp f g) = Imp (qmerge f) (qmerge g)
qmerge (Iff f g) = Iff (qmerge f) (qmerge g)
qmerge (Fa vs (Fa ws f)) = Fa (vs ++ ws) $ qmerge f
qmerge (Ex vs (Ex ws f)) = Ex (vs ++ ws) $ qmerge f
qmerge (Fa vs f) = Fa vs $ qmerge f
qmerge (Ex vs f) = Ex vs $ qmerge f
qmerge f = f

fltn :: Form -> Form
fltn (Not f) = Not $ fltn f
fltn (Or fs) = Or $ flatOr $ L.map fltn fs
fltn (And fs) = And $ flatAnd $ L.map fltn fs
fltn (Imp f g) = Imp (fltn f) (fltn g)
fltn (Iff f g) = Iff (fltn f) (fltn g)
fltn (Fa vs f) = Fa vs $ fltn f
fltn (Ex vs f) = Ex vs $ fltn f
fltn f = f

uws :: Form -> Form
uws (Not f) = Not $ uws f
uws (Or [f]) = uws f
uws (Or fs) = Or $ L.map uws fs
uws (And [f]) = uws f
uws (And fs) = And $ L.map uws fs
uws (Imp f g) = Imp (uws f) (uws g)
uws (Iff f g) = Iff (uws f) (uws g)
uws (Fa vs f) = Fa vs $ uws f
uws (Ex vs f) = Ex vs $ uws f
uws f = f

flatSimp :: Form -> Form
flatSimp (Not f) = Not $ flatSimp f
flatSimp (Or fs) = 
  case flatOr $ L.map flatSimp fs of 
    [f] -> f 
    fs' -> if Top `elem` fs' 
           then Top 
           else Or fs'
flatSimp (And fs) = 
  case flatAnd $ L.map flatSimp fs of 
    [f] -> f 
    fs' -> if Bot `elem` fs' 
           then Bot 
           else And fs'
flatSimp (Imp f g) = Imp (flatSimp f) (flatSimp g)
flatSimp (Iff f g) = Iff (flatSimp f) (flatSimp g)
flatSimp (Fa vs f) = Fa vs $ flatSimp f
flatSimp (Ex vs f) = Ex vs $ flatSimp f
flatSimp f = f

nnf :: Bool -> Form -> Form
nnf ex (Not (Not f)) = nnf ex f
nnf ex (Not Top) = Bot
nnf ex (Not Bot) = Top
nnf ex (Not (Or fs)) = And $ L.map (nnf ex . Not) fs
nnf ex (Not (And fs)) = Or $ L.map (nnf ex . Not) fs
nnf ex (Not (Imp f g)) = nnf ex (And [Not g, f])
nnf True (Not (Iff f g)) = Not $ nnf True (Iff f g)
nnf False (Not (Iff f g)) =
  let nn = nnf False (Not g) in
  let nm = nnf False (Not f) in
  let pn = nnf False g in
  let pm = nnf False f in
  And [Or [nn, nm], Or [pn, pm]]
nnf ex (Not (Fa vs f)) = Ex vs (nnf ex $ Not f)
nnf ex (Not (Ex vs f)) = Fa vs (nnf ex $ Not f)
nnf ex (Or fs)  = Or  $ L.map (nnf ex) fs
nnf ex (And fs) = And $ L.map (nnf ex) fs
nnf ex (Imp f g) = Or [nnf ex g, nnf ex $ Not f]
nnf True  (Iff f g) = Iff (nnf True f) (nnf True g)
nnf False (Iff f g) =
  let nn = nnf False (Not g) in
  let nm = nnf False (Not f) in
  let pn = nnf False g in
  let pm = nnf False f in
  And [Or [pm, nn], Or [pn, nm]]
nnf ex (Fa vs f) = Fa vs $ nnf ex f
nnf ex (Ex vs f) = Ex vs $ nnf ex f

nnf ex (Not (Rel r xs)) = Not $ Rel r xs
nnf ex (Not (Eq x y)) = Not $ Eq x y
nnf ex Top = Top
nnf ex Bot = Bot
nnf ex (Rel r xs) = Rel r xs
nnf ex (Eq x y) = Eq x y

delVacVars :: Form -> Form
delVacVars (Not f) = Not $ delVacVars f
delVacVars (Fa vs f) =
  case L.filter (`varInf` f) vs of
    [] -> delVacVars f
    vs' -> Fa vs' $ delVacVars f
delVacVars (Ex vs f) =
  case L.filter (`varInf` f) vs of
    [] -> delVacVars f
    vs' -> Ex vs' $ delVacVars f
delVacVars (Imp f g) = Imp (delVacVars f) (delVacVars g)
delVacVars (Iff f g) = Iff (delVacVars f) (delVacVars g)
delVacVars (Or fs) = Or $ L.map delVacVars fs
delVacVars (And fs) = And $ L.map delVacVars fs
delVacVars f@Top = f
delVacVars f@Bot = f
delVacVars f@(Rel _ _) = f
delVacVars f@(Eq _ _) = f

ppr :: Set Funct -> Bool -> Form -> Form
ppr rs b (Not f) = Not $ ppr rs (not b) f 
ppr rs b (Or fs) = Or $ L.map (ppr rs b) fs
ppr rs b (And fs) = And $ L.map (ppr rs b) fs
ppr rs b (Imp f g) = Imp (ppr rs (not b) f) (ppr rs b g)
ppr rs b f@(Iff _ _) = f
ppr rs b (Fa vs f) = Fa vs $ ppr rs b f
ppr rs b (Ex vs f) = Ex vs $ ppr rs b f
ppr rs b f@(Rel r _) 
  | S.member r rs = if b then Top else Bot
  | otherwise = f
ppr rs _ f@(Eq _ _) = f
ppr rs _ f@Bot = f
ppr rs _ f@Top = f