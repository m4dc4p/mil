{-# LANGUAGE GADTs #-}

module Util

where

import Text.PrettyPrint 
import Compiler.Hoopl

vcat' :: [Doc] -> Doc
vcat' = foldl ($+$) empty

commaSep = punctuated comma 
spaced = punctuated space 
texts = map text

punctuated :: Doc -> (a -> Doc) -> [a] -> Doc
punctuated sep f = hcat . punctuate sep . map f

-- | Use the printer given when j is a Just value,
-- otherwise use the empty document.
maybeP :: (a -> Doc) -> Maybe a -> Doc
maybeP j = maybe empty j 

printFB :: (IsMap map) => ((KeyOf map, a) -> Doc) -> map a -> Doc
printFB p = vcat . map p . mapToList

type Name = String
type Var = String
type Constructor = String

data Alt e = Alt Constructor [Name] e
  deriving (Show, Eq)

-- Hoopl utilities

maybeC :: a -> (n -> a) -> MaybeC e1 n -> a
maybeC _ f (JustC e) = f e
maybeC def f _ = def 

maybeO :: a -> (n -> a) -> MaybeO e1 n -> a
maybeO def f (JustO b) = f b
maybeO def f _ = def

maybeGraphCC :: b -> (block node C C -> b) -> Graph' block node C C -> [b]
maybeGraphCC b f (GMany _ middles _) = map f . mapElems $ middles
