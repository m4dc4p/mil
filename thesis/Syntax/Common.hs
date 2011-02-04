{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
module Syntax.Common (module Syntax.Common, SourcePos, newPos) where

import Control.Monad.Error
import Data.List
import Text.Parsec.Pos

-- 

type Id = String

data Literal = Numeric Integer
             | BitVector Integer Int 
             | Field Id 
               deriving Show

--

data Kind = KVar Id 
          | KFun Kind Kind 
          | KStar 
          | KNat 
          | KArea 
          | KLabel Id 
            deriving (Eq, Show)

data Kinded t = Kinded t Kind

instance Eq t => Eq (Kinded t)
    where Kinded t _ == Kinded t' _ = t == t'

instance Ord t => Ord (Kinded t)
    where compare (Kinded t _) (Kinded t' _) = compare t t'

-- 

data Located t = At SourcePos t
               deriving Show

instance Functor Located
    where fmap f (At p t) = At p (f t)

at :: Located t -> u -> Located u
at (At p _) u = At p u

dislocate :: Located t -> t 
dislocate (At _ t) = t

introduced :: t -> Located t
introduced = At (newPos "<introduced>" 0 0)

-- We use pairs of a possible source position and string as errors

instance Error (Maybe SourcePos, String)
    where strMsg s = (Nothing, s)
          noMsg    = (Nothing, "")

--

data Flag = Holds | Fails
          deriving (Eq, Show)

data Ctor p t = Ctor (Located Id) [Located p] [Located t]
            deriving Show

data Fundep t = [t] :~> [t]
            deriving Show

determined :: Eq t => [Fundep t] -> [t] -> [t]
determined fds xs0 = loop xs0
    where loop xs | all (`elem` xs) xs' = xs'
                  | otherwise           = loop xs'
              where xs' = foldl apply xs fds
                    apply xs' (xs :~> ys) | all (`elem` xs') xs = filter (`notElem` xs') ys ++ xs'
                                          | otherwise           = xs'

--

class Binder t
    where bound :: t -> [Id]

withoutBound :: Binder t => t -> [Id] -> [Id]
withoutBound t = (\\ bound t)

instance Binder t => Binder [t]
    where bound = concatMap bound

instance Binder t => Binder (Maybe t)
    where bound = maybe [] bound

instance Binder t => Binder (Located t)
    where bound (At _ t) = bound t

--

class HasVariables t 
    where freeVariables :: t -> [Id]

instance HasVariables t => HasVariables [t]
    where freeVariables = concatMap freeVariables

instance HasVariables t => HasVariables (Maybe t) 
    where freeVariables = maybe [] freeVariables

instance HasVariables t => HasVariables (Located t)
    where freeVariables (At _ t) = freeVariables t
