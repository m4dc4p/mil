{-# LANGUAGE GeneralizedNewtypeDeriving, TypeSynonymInstances #-}
module Printer.Common (module Printer.Common, SimpleDoc, displayS, displayIO, Fixity(..)) where

import Control.Monad.Reader
import Data.Char
import qualified Data.Map as Map
import Printer.WadlerLeijen (SimpleDoc, displayS, displayIO) 
import qualified Printer.WadlerLeijen as WL
import Syntax.Common
import Syntax.FPE (Assoc(..), dislocate, Fixity(..), Fixities(..), Id, Located(..), mergeFixities)

-- Following Iavor's lead, basically wrapping the pretty-printing library of my choice (in this
-- case, the Wadler-Leijen "prettier printer") in a reader monad to capture details like the current
-- precendence, display options, etc.

newtype Printer t = Printer { runPrinter :: Reader PrinterOptions t }
    deriving (Functor, Monad, MonadReader PrinterOptions)

data PrinterOptions = PO { precendence :: Int
                         , fixities :: Fixities }

defaultOptions = PO 0 (Fixities Map.empty Map.empty)

type Doc = Printer WL.Doc

-- The prettier printer

p1 <> p2        = liftM2 (WL.<>) p1 p2
p1 <+> p2       = liftM2 (WL.<+>) p1 p2
p1 </> p2       = liftM2 (WL.</>) p1 p2
p1 <//> p2      = liftM2 (WL.<//>) p1 p2
p1 <$> p2       = liftM2 (WL.<$>) p1 p2
p1 <$$> p2      = liftM2 (WL.<$$>) p1 p2

infixr 5 </>, <//>, <$>, <$$>
infixr 6 <>, <+>

list, tupled, semiBraces :: [Doc] -> Doc
list            = liftM WL.list . sequence
tupled          = liftM WL.tupled . sequence
semiBraces      = liftM WL.semiBraces . sequence

punctuate :: Doc -> [Doc] -> [Doc]
punctuate p []     = []
punctuate p [d]    = [d]
punctuate p (d:ds) = (d <> p) : (punctuate p ds)

sep, fillSep, hsep, vsep :: [Doc] -> Doc
sep             = liftM WL.sep . sequence
fillSep         = liftM WL.fillSep . sequence
hsep            = liftM WL.hsep . sequence
vsep            = liftM WL.vsep . sequence

cat, fillCat, hcat, vcat :: [Doc] -> Doc
cat             = liftM WL.cat . sequence
fillCat         = liftM WL.fillCat . sequence
hcat            = liftM WL.hcat . sequence
vcat            = liftM WL.vcat . sequence

softline, softbreak :: Doc
softline        = return WL.softline
softbreak       = return WL.softbreak

squotes, dquotes, braces, parens, angles, brackets :: Doc -> Doc
squotes         = liftM WL.squotes
dquotes         = liftM WL.dquotes
braces          = liftM WL.braces
parens          = liftM WL.parens
angles          = liftM WL.angles
brackets        = liftM WL.brackets

lparen, rparen, langle, rangle, lbrace, rbrace, lbracket, rbracket :: Doc
lparen          = return WL.lparen
rparen          = return WL.rparen
langle          = return WL.langle
rangle          = return WL.rangle
lbrace          = return WL.lbrace
rbrace          = return WL.rbrace
lbracket        = return WL.lbracket
rbracket        = return WL.rbracket

squote, dquote, semi, colon, comma, space, dot, backslash, equals :: Doc
squote          = return WL.squote
dquote          = return WL.dquote
semi            = return WL.semi
colon           = return WL.colon
comma           = return WL.comma
space           = return WL.space
dot             = return WL.dot
slash           = char '/'
backslash       = return WL.backslash
equals          = return WL.equals
bar             = char '|'

string :: String -> Doc
string          = return . WL.string
                  
bool :: Bool -> Doc
bool            = return . WL.bool

int :: Int -> Doc                  
int             = return . WL.int

integer :: Integer -> Doc
integer         = return . WL.integer

float :: Float -> Doc
float           = return . WL.float

double :: Double -> Doc
double          = return . WL.double

rational :: Rational -> Doc
rational        = return . WL.rational

indent, hang, nest :: Int -> Doc -> Doc
indent i        = liftM (WL.indent i)
hang i          = liftM (WL.hang i)
nest i          = liftM (WL.nest i)
                  
align :: Doc -> Doc
align           = liftM WL.align

empty :: Doc
empty           = return WL.empty

char :: Char -> Doc
char            = return . WL.char

text :: String -> Doc
text            = return . WL.string

line, linebreak :: Doc
line            = return WL.line
linebreak       = return WL.linebreak

-- New combinators

withPrecedence :: Int -> Doc -> Doc
withPrecedence n d = local (\po -> po { precendence = n }) d

atPrecendence :: Int -> Doc -> Doc
atPrecendence n d = 
    do prec <- asks precendence
       if prec <= n then withPrecedence n d else parens (withPrecedence n d)

valFixity, typeFixity :: Id -> Printer Fixity
valFixity id = asks (maybe (Fixity LeftAssoc 9) dislocate . Map.lookup id . valFixities . fixities)
typeFixity id = asks (maybe (Fixity LeftAssoc 9) dislocate . Map.lookup id . typeFixities . fixities)
eitherFixity id = do fs <- asks fixities
                     case (Map.lookup id (valFixities fs), Map.lookup id (typeFixities fs)) of
                       (Just f, _) -> return (dislocate f)
                       (Nothing, Just f) -> return (dislocate f)
                       (Nothing, Nothing) -> return (Fixity LeftAssoc 9)

withFixities :: Fixities -> Printer t -> Printer t
withFixities f d = local (\po -> po { fixities = mergeFixities f (fixities po) }) d

-- Rendering

data Renderer = Compact | Pretty Float Int 

render :: PrinterOptions -> Renderer -> Doc -> SimpleDoc
render options Compact d          = WL.renderCompact (runReader (runPrinter d) options)
render options (Pretty rfrac w) d = WL.renderPretty rfrac w (runReader (runPrinter d) options)

instance Show Doc
    where showsPrec _ d = displayS (render defaultOptions (Pretty 0.4 120) d)

quoted :: Printable t => t -> String
quoted = show . squotes . ppr

-- Overloading

class Printable t
    where ppr :: t -> Doc

-- Common instances

instance Printable t => Printable (Located t)
    where ppr (At _ t) = ppr t

instance Printable Literal
    where ppr (Numeric i) = integer i
          ppr (BitVector val size) = char 'B' <> text padding <> text (toBits val log2)
              where log2 = floor (log (fromIntegral val) / log 2)
                    padding = replicate (size - log2 - 1) '0'
                    toBits 0 0 = "0"
                    toBits 1 0 = "1"
                    toBits n k | n >= 2 ^ k = '1' : toBits (n - 2 ^ k) (k - 1)
                               | otherwise = '0' : toBits n (k - 1)
          ppr (Field s) = char '#' <> text s

instance Printable Kind
    where ppr (KVar id) = text id
          ppr KStar = char '*'
          ppr KNat = text "nat"
          ppr KArea = text "area"
          ppr (KLabel s) = char '*' <> text s
          ppr (KFun lhs rhs) = atPrecendence 0 (withPrecedence 1 (ppr lhs) <+> text "->" <+> ppr rhs)

symbol s@(c:_)
    | s == "()" = text s
    | not (isAlpha c || isNumber c) = parens (text s)
    | otherwise = text s

instance Printable String
    where ppr = symbol

