module Mustache

import TParsec
import TParsec.NEList
import Data.SortedSet

%default total

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
  go acc []                         = string acc []
  go acc ('\\' :: '\\' :: cs)       = go ('\\' :: acc) cs
  go acc ('\\' :: '{' :: '{' :: cs) = go ('{' :: '{' :: acc) cs
  go acc ('\\' :: '}' :: '}' :: cs) = go ('}' :: '}' :: acc) cs
  go acc (        '{' :: '{' :: cs) = LDCBRACE :: string acc (go [] cs)
  go acc (        '}' :: '}' :: cs) = RDCBRACE :: string acc (go [] cs)
  go acc (c :: cs)                  = go (c :: acc) cs

data Mustache : SortedSet String -> Type where
  Nothing : Mustache SortedSet.empty
  PHolder : (tag : String) -> Mustache s -> Mustache (insert tag s)
  Content : String -> Mustache s -> Mustache s

ExMustache : Type
ExMustache = (s : SortedSet String ** Mustache s)

DExMustache : Type
DExMustache = ExMustache -> ExMustache

toExMustache : DExMustache -> ExMustache
toExMustache f = f (empty ** Nothing)

MustacheParser : Type -> Nat -> Type
MustacheParser = Parser (SizedList Tok) Tok Maybe

isSTRING : Tok -> Maybe String
isSTRING (STRING s) = Just s
isSTRING _          = Nothing

aSTRING : All (MustacheParser String)
aSTRING = guardM isSTRING anyTok

tag : All (MustacheParser String)
tag = between (exact LDCBRACE) (exact RDCBRACE) aSTRING

block : All (MustacheParser DExMustache)
block =
  alt (map (\ s, (set ** mstch) => (insert s set ** PHolder s mstch)) tag)
      (map (\ s, (set ** mstch) => (set          ** Content s mstch)) aSTRING)

mustache : All (MustacheParser ExMustache)
mustache = map (toExMustache . NEList.foldr1 (.)) $ nelist block
