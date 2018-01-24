module TMustache.Parser

import TParsec
import TParsec.SizedDict
import TParsec.NEList

import TMustache.Data.Map as Map
import TMustache.Relation.Order.Instances

import TMustache.Data.Star
import TMustache.Data.DiffExists

import TMustache.Valuation
import TMustache.TMustache

%default total
%access public export

data Tok : Type where
  LDCBRACE : Tok            -- Left  Double Curly Braces
  RDCBRACE : Tok            -- Right Double Curly Braces
  STRING   : String -> Tok  -- Raw String

injectiveSTRING : STRING s = STRING t -> s = t
injectiveSTRING Refl = Refl

implementation DecEq Tok where

  decEq LDCBRACE   LDCBRACE   = Yes Refl
  decEq RDCBRACE   RDCBRACE   = Yes Refl
  decEq (STRING s) (STRING t) with (decEq s t)
    | Yes pr = Yes (cong pr)
    | No  pr = No (\ eq => pr (injectiveSTRING eq))
  decEq LDCBRACE   RDCBRACE   = No (\ eq => case eq of Refl impossible)
  decEq LDCBRACE   (STRING _) = No (\ eq => case eq of Refl impossible)
  decEq RDCBRACE   LDCBRACE   = No (\ eq => case eq of Refl impossible)
  decEq RDCBRACE   (STRING _) = No (\ eq => case eq of Refl impossible)
  decEq (STRING _) RDCBRACE   = No (\ eq => case eq of Refl impossible)
  decEq (STRING _) LDCBRACE   = No (\ eq => case eq of Refl impossible)

tokenize : String -> List Tok
tokenize = go [] . unpack where

  string : List Char -> List Tok -> List Tok
  string [] ts = ts
  string cs ts = STRING (pack $ List.reverse cs) :: ts

  go : List Char -> List Char -> List Tok
  go acc []                 = string acc []
  go acc ('\\' :: c :: cs)  = go (c :: acc) cs
  go acc ('{' :: '{' :: cs) = string acc $ LDCBRACE :: go [] cs
  go acc ('}' :: '}' :: cs) = string acc $ RDCBRACE :: go [] cs
  go acc (c :: cs)          = go (c :: acc) cs

MustacheParser : Type -> Nat -> Type
MustacheParser = Parser (SizedList Tok) Tok List

isSTRING : Tok -> Maybe String
isSTRING (STRING s) = Just s
isSTRING _          = Nothing

aSTRING : All (MustacheParser String)
aSTRING = guardM isSTRING anyTok

ExMustacheBlock : Type
ExMustacheBlock = DiffExists (Map StringLT MkType) MustacheBlock

pCond : String -> ExMustache -> ExMustacheBlock
pCond label (MkDiffExists f p) =
  let diff = override label MkBool in
  MkDiffExists (f . diff) (\ i => PCond label (p (diff i)))

pHolder : String -> ExMustacheBlock
pHolder label = MkDiffExists (override label MkString) (\ i => PHolder label)

content : String -> ExMustacheBlock
content str = MkDiffExists (\ i => i) (\ i => Content str)

mustacheBlock : All (Box (MustacheParser ExMustache) :-> MustacheParser ExMustacheBlock)
mustacheBlock rec = alt (map content aSTRING) $
  rand (exact LDCBRACE) $ bind aSTRING $ \ str =>
  case unpack str of
    '#' :: rest => let label = pack rest in
      Combinators.map (pCond label) $ land (rand (exact RDCBRACE) rec)
                                    $ and (exact LDCBRACE)
                                    $ land (exact (STRING ("/" <+> label)))
                                    $ exact RDCBRACE
    _           => cmap (pHolder str) $ exact RDCBRACE

empty : ExMustache
empty = MkDiffExists (\ i => i) (\ i => [])

mustache : All (MustacheParser ExMustache)
mustache = fix _ $ \ rec =>
  Combinators.map (foldr (combine (::)) empty) $ nelist (mustacheBlock rec)

parseMustache : String -> Maybe ExMustache
parseMustache str =
  let res = runParser mustache lteRefl $ MkSizedType MkSizedDict (tokenize str) Refl in
  case filter (\ r => Size r == Z) res of
    r :: _ => Just (Value r)
    _      => Nothing
