{-# LANGUAGE GADTs #-}

module Util

where

import Text.PrettyPrint 
import Compiler.Hoopl

vcat' :: [Doc] -> Doc
vcat' = foldl ($+$) empty

commaSep = punctuated (comma <> space)
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

altE :: Alt e -> e
altE (Alt _ _ e) = e

-- | Insert the element given at the position
-- specified in the list. Positoin is 0-based,
-- with the element inserted BEFORE the corresponding
-- element in the list. If the index is too high (or too
-- low), the original list is returned instead. 
--
-- Examples: 
--   insertAt ["a"] 0 "b" == ["b", "a"]
--   insertAt ["a"] 1 "b" == ["a", "b"]
--   insertAt ["a"] 2 "b" == ["a"]
--   insertAt [] 0 "b" == ["b"]
--   insertAt [] 1 "b" == []
--   insertAt ["a"] (-1) "b" == ["a"]

insertAt :: [a] -> Int -> a -> [a]
insertAt elems idx elem = insertAt' elems idx
  where
    insertAt' es n 
      | n == 0 = elem : es
      | n < 0 = []
      | null es = []
    insertAt' (e:es) n = e : insertAt' es (n - 1)
-- Hoopl utilities

-- | maybe function for closed nodes.
maybeC :: a -> (n -> a) -> MaybeC e1 n -> a
maybeC _ f (JustC e) = f e
maybeC def f _ = def 

-- | maybe functin for open nodes.
maybeO :: a -> (n -> a) -> MaybeO e1 n -> a
maybeO def f (JustO b) = f b
maybeO def f _ = def

-- This function seems badly defined - it doesn't use
-- the b argument.
maybeGraphCC :: b -> (block node C C -> b) -> Graph' block node C C -> [b]
maybeGraphCC b f (GMany _ middles _) = map f . mapElems $ middles

-- | Run a Hoopl optimization pas with infinite fuel,
-- using the monad Hoopl provides.
runSimple :: SimpleFuelMonad a -> a
runSimple p = runSimpleUniqueMonad $ runWithFuel infiniteFuel p

