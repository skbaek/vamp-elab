module Norm where 

import Types
import Basic

import Data.Text.Lazy as T ( Text )
import Data.Set as S ( Set, member )

import Data.List as L

boolSimp :: Form -> Form
boolSimp (Rel r xs) = Rel r xs
boolSimp (Eq x y) = Eq x y
boolSimp (Not f) =
  case boolSimp f of
    And [] -> Or []
    Or [] -> And []
    g -> Not g
boolSimp (Or fs) =
  let gs = L.map boolSimp fs in
  if top `elem` gs 
    then top
    -- else case L.filter (/= bot) gs of
    --        [g] -> g
    --        hs -> Or hs
    else Or $ L.filter (/= bot) gs 
boolSimp (And fs) =
  let gs = L.map boolSimp fs in
  if bot `elem` gs 
    then bot
    -- else case L.filter (/= top) gs of
    --        [g] -> g
    --        hs -> And hs
    else And $ L.filter (/= top) gs 
boolSimp (Fa vs f) =
  case boolSimp f of
    And [] -> And []
    Or [] -> Or []
    g -> Fa vs g
boolSimp (Ex vs f) =
  case boolSimp f of
    And [] -> And []
    Or [] -> Or []
    g -> Ex vs g
boolSimp (Imp f g) =
  case (boolSimp f, boolSimp g) of
    (Or [], _) -> top
    (_, And []) -> top
    (And [], g_) -> g_
    (f_, Or []) -> Not f_
    (f', g') -> Imp f' g'
boolSimp (Iff f g) =
  case (boolSimp f, boolSimp g) of
    (And [], g') -> g'
    (f', And []) -> f'
    (Or [], g') -> Not g'
    (f', Or []) -> Not f'
    (f', g') -> Iff f' g'

flatOr :: [Form] -> [Form]
flatOr [] = []
flatOr (Or [] : fs) = flatOr fs
flatOr (Or fs : gs) = flatOr fs ++ flatOr gs
flatOr (f : fs) = f : flatOr fs

flatAnd :: [Form] -> [Form]
flatAnd [] = []
flatAnd (And [] : fs) = flatAnd fs
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
    fs' -> if top `elem` fs' 
           then top 
           else Or fs'
flatSimp (And fs) = 
  case flatAnd $ L.map flatSimp fs of 
    [f] -> f 
    fs' -> if bot `elem` fs' 
           then bot 
           else And fs'
flatSimp (Imp f g) = Imp (flatSimp f) (flatSimp g)
flatSimp (Iff f g) = Iff (flatSimp f) (flatSimp g)
flatSimp (Fa vs f) = Fa vs $ flatSimp f
flatSimp (Ex vs f) = Ex vs $ flatSimp f
flatSimp f = f

nnf :: Bool -> Form -> Form
nnf ex (Not (Not f)) = nnf ex f
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
  | S.member r rs = if b then And [] else Or []
  | otherwise = f
ppr rs _ f@(Eq _ _) = f

{-
ppr :: Set Text -> Bool -> Form -> Form
ppr rs b (Not f) =
  let f' = ppr rs (not b) f in
  case f' of
    And [] -> Or []
    Or [] -> And []
    _ -> Not f'
ppr rs b (Or fs) =
  let fs' = flatOr (L.map (ppr rs b) fs) in
  if And [] `elem` fs'
  then And []
  else case L.filter (Or [] /=) fs' of
         [f] -> f
         fs'' -> Or fs''
ppr rs b (And fs) =
  let fs' = flatAnd (L.map (ppr rs b) fs) in
  if Or [] `elem` fs'
  then Or []
  else case L.filter (And [] /=) fs' of
         [f] -> f
         fs'' -> And fs''
ppr rs b (Imp f g) =
  let f' = ppr rs (not b) f in
  let g' = ppr rs b g in
  case (f', g') of
    (And [], _) -> g'
    (Or [], _) -> And []
    (_, And []) -> And []
    (_, Or []) -> Not f'
    _ -> Imp f' g'
ppr rs b f@(Iff _ _) = f
ppr rs b (Fa vs f) =
  case ppr rs b f of
    And [] -> And []
    Or [] -> Or []
    Fa ws f' -> Fa (vs ++ ws) f'
    f' -> Fa vs f'
ppr rs b (Ex vs f) =
  case ppr rs b f of
    And [] -> And []
    Or [] -> Or []
    Ex ws f' -> Ex (vs ++ ws) f'
    f' -> Ex vs f'
ppr rs b f@(Rel r _) =
  if S.member r rs
  then if b then And [] else Or []
  else f
ppr rs _ f@(Eq _ _) = f
-}