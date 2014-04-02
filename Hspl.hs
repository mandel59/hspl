{-# LANGUAGE ScopedTypeVariables, ViewPatterns #-}

module Hspl where

import Control.Applicative ((<$>), (<*>), (<|>))
import qualified Control.Applicative as App
import Control.Monad ((>=>))
import Control.Monad.Identity (runIdentity)
import qualified Control.Monad.State as State
import qualified Control.Monad.Trans.List as LT
import Data.Char (isAlpha, isLower, isPrint, ord)
import Data.List (intersperse)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, maybe)
import Numeric (showHex)

newtype ID = ID String
           deriving (Eq, Ord, Show)

viewID :: ID -> String
viewID (ID s) = s

data Variable = VI ID
              | VA Int
              deriving (Eq, Ord, Show)

var :: String -> Variable
var s = VI (ID s)

newVar :: Monad m => State.StateT Int m Variable
newVar = do
  n <- State.get
  State.put (n + 1)
  return (VA n)

tVar :: String -> Term
tVar = TVar . var

prettyVar :: Subst -> Variable -> ShowS
prettyVar s (VI (ID i)) ss = i ++ ss
prettyVar s (VA n) ss =
  case Map.lookup (VA n) s of
    Nothing -> "_" ++ show n ++ ss
    Just t -> prettyTerm s t ss

type Function = (ID, [Term])

atom :: String -> Function
atom s = (ID s, [])

tAtom :: String -> Term
tAtom = TFun . atom

comp :: String -> [Term] -> Function
comp s ts = (ID s, ts)

tComp :: String -> [Term] -> Term
tComp s ts = TFun (comp s ts)

prettyAtom :: String -> ShowS
prettyAtom s ss
  | null s = "''" ++ ss
  | isLower (head s) && all isAlpha s = s ++ ss
  | otherwise = "'" ++ escape s ++ "'" ++ ss where
    escape :: String -> String
    escape "" = ""
    escape ('\\' : s) = "\\\\" ++ escape s
    escape ('\'' : s) = "\\'" ++ escape s
    escape ('\n' : s) = "\\n" ++ escape s
    escape ('\r' : s) = "\\r" ++ escape s
    escape ('\t' : s) = "\\t" ++ escape s
    escape ('\v' : s) = "\\v" ++ escape s
    escape (c : s)
      | isPrint c = c : escape s
      | otherwise = "\\x" ++ showHex (ord c) ("\\" ++ escape s)

prettyFun :: Subst -> Function -> ShowS
prettyFun s (ID i, []) ss = prettyAtom i ss
prettyFun s (ID i, xs) ss = prettyAtom i ("(" ++ showArgs xs (")" ++ ss)) where
  showArgs [] ss = ss
  showArgs (x : xs) ss = prettyTerm s x (", " ++ showArgs xs ss)

data Term = TVar Variable
          | TFun Function
          | TInt Int
          deriving (Show)

tNil :: Term
tNil = TFun (atom "[]")

tCons :: Term -> Term -> Term
tCons x xs = TFun (comp "." [x, xs])

tList :: [Term] -> Term
tList = foldr tCons tNil

isList :: Term -> Bool
isList (TFun (viewID -> "[]", [])) = True
isList (TFun (viewID -> ".", [_, TVar y])) = True
isList (TFun (viewID -> ".", [_, xs])) = isList xs
isList _ = False

prettyList :: Subst -> Term -> ShowS
prettyList s l ss = "[" ++ elems' l ("]" ++ ss) where
  elems' (TFun (viewID -> "[]", [])) ss = ss
  elems' (TFun (viewID -> ".", [x, TVar y])) ss
    | VA _ <- y
    , Just t <- Map.lookup y s
    , isList t = prettyTerm s x (elems'' t ss)
    | otherwise = prettyTerm s x (" | " ++ prettyVar s y ss)
  elems' (TFun (viewID -> ".", [x, xs])) ss = prettyTerm s x (elems'' xs ss)
  elems'' (TFun (viewID -> "[]", [])) ss = ss
  elems'' l ss = ", " ++ elems' l ss
  
prettyTerm :: Subst -> Term -> ShowS
prettyTerm s (TVar x) = prettyVar s x
prettyTerm s (TFun f)
  | isList (TFun f) = prettyList s (TFun f)
  | otherwise = prettyFun s f
prettyTerm _ (TInt i) = shows i

type Rule = (Function, [Function])

type Subst = Map.Map Variable Term

subst :: Subst -> Term -> Term
subst s t = subst' t where
  subst' (TVar x) = fromMaybe (TVar x) (Map.lookup x s)
  subst' (TFun (f, xs)) = TFun (f, map subst' xs)
  subst' t = t

prettySubst :: Subst -> ShowS
prettySubst s ss =
  let s' = Map.assocs s in
  if null s'
  then "true" ++ ss
  else
    let s'' = concatMap (\(k, v) ->
                    case k of
                      VI _ ->
                        [\ss -> prettyVar s k (" = " ++ prettyTerm s v ss)]
                      VA _ ->
                        []) s' in
    foldr ($) ss (intersperse (\ss -> ",\n" ++ ss) s'')

compose :: Subst -> Subst -> Subst
compose s s0 = Map.union (Map.map (subst s0) s) s0

empty :: Subst
empty = Map.empty

singleton :: Variable -> Term -> Subst
singleton = Map.singleton

occur :: Variable -> Term -> Bool
occur x (TVar y) | x == y = True
occur x (TFun (g, ys)) = any (occur x) ys
occur x _ = False

mapBoth :: (a -> b) -> (a, a) -> (b, b)
mapBoth f (x, y) = (f x, f y)

unify :: [(Term, Term)] -> Subst -> Maybe Subst
unify eql s = solve (substEql s eql) s where
  substEql :: Subst -> [(Term, Term)] -> [(Term, Term)]
  substEql s = map (mapBoth $ subst s)
  insert :: Variable -> Term -> Subst -> [(Term, Term)] -> Maybe Subst
  insert x t s es = let s0 = singleton x t in
    solve (substEql s0 es) (compose s0 s)
  solve :: [(Term, Term)] -> Subst -> Maybe Subst
  solve [] s = Just s
  solve (e : es) s = case e of
    (TVar x, TVar y)
      | x == y -> solve es s
    (TVar x, t)
      | not (occur x t) -> insert x t s es
    (t, TVar x)
      | not (occur x t) -> insert x t s es
    (TFun (f, xs), TFun (g, ys))
      | f == g && length xs == length ys -> solve ((zip xs ys) ++ es) s
    (TInt i, TInt j)
      | i == j -> solve es s
    (_, _) -> Nothing

newFun :: Monad m => [Term] -> [Function] -> State.StateT Int m ([Term], [Function])
newFun args defs = State.evalStateT newFun' Map.empty
  where
    newFun' = do
      a <- mapM newT' args
      d <- mapM newF' defs
      return (a, d)
    newF' (f, xs) = do
      ys <- mapM newT' xs
      return (f, ys)
    newT' (TVar x) = do
      m <- State.get
      y <- case Map.lookup x m of
        Nothing -> do
          y <- State.lift $ newVar
          State.put (Map.insert x y m)
          return y
        Just y -> return y
      return (TVar y)
    newT' (TFun (f, xs)) = do
      ys <- mapM newT' xs
      return (TFun (f, ys))
    newT' t = return t

eval :: (App.Applicative m, Monad m) => Function -> [Rule] -> Subst -> State.StateT Int (LT.ListT m) Subst
eval ((viewID -> "false"), []) _ s = App.empty
eval ((viewID -> "true"), []) _ s = return s
eval ((viewID -> "="), [x, y]) _ s = maybe App.empty return (unify [(x, y)] s)
eval ((viewID -> ","), [TFun f, TFun g]) rs s =
  (eval f rs >=> eval g rs) s
eval ((viewID -> ";"), [TFun f, TFun g]) rs s =
  eval f rs s <|> eval g rs s
eval (f, xs) rules s = eval' rules where
  eval' [] = App.empty
  eval' (((g, ys), hs) : rs)
    | f == g && length xs == length ys = do
      (ys', hs') <- newFun ys hs
      let s' = maybe App.empty return (unify (zip xs ys') s)
          eval'' = foldr (>=>) return (map (\h -> eval h rules) hs') in
        (s' >>= eval'') <|> eval' rs

evaltop :: Function -> [Rule] -> [Subst]
evaltop f rs = runIdentity (LT.runListT (State.evalStateT (eval f rs empty) 0))
