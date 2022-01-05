{-
  Day 2 task of https://adventofcode.com/
-}
module a2 where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String; primShowNat; primStringAppend)

open import Data.Nat
open import Data.Bool using (if_then_else_)
open import Data.List
open import Data.Maybe

postulate putStrLn : String → IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC putStrLn = putStrLn . T.unpack #-}

data Command : Set where
  forward : ℕ → Command
  up      : ℕ → Command
  down    : ℕ → Command

record Position : Set where
  field
    horizontal : ℕ
    depth : ℕ

open Position

apply : Command → Position → Maybe Position

apply (forward x) record { horizontal = h ;     depth = d }       =
             just record { horizontal = h + x ; depth = d }

apply (up x)      record { horizontal = h ;     depth = d }       =
        if d <ᵇ x
        then nothing
        else just record { horizontal = h ;     depth = ∣ d - x ∣ }

apply (down x)    record { horizontal = h ;     depth = d }       =
             just record { horizontal = h ;     depth = d + x }


main : IO ⊤
main = {!!} -- putStrLn (primShowNat (doTask2 input))
