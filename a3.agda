{-
  Day 3, 1st part
-}
module a3 where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String; primShowNat)
open import Agda.Builtin.Equality

open import Function

open import Data.Nat
open import Data.Bool
open import Data.List hiding (lookup;allFin)
                      renaming (map to mapList)
open import Data.Vec
open import Data.Fin hiding (_+_)
open import Data.Maybe renaming (map to maybeMap)

open import a3-input

postulate putStrLn : String → IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC putStrLn = putStrLn . T.unpack #-}

-- helper
showMaybeNat : Maybe ℕ → String
showMaybeNat (just n) = primShowNat n
showMaybeNat nothing = "nothing"

BitVec = Vec ℕ

findMostCommonBit : {n : ℕ} (index : Fin n) → List (BitVec n) → Maybe ℕ
findMostCommonBit {n = n} index input = iterate 0 0 input
  where eval : BitVec n → Maybe ℕ
        eval v with lookup v index
        ...        | 0 = just 0
        ...        | 1 = just 1
        ...        | _ = nothing

        iterate : (zeros : ℕ) (ones : ℕ) → List (BitVec n) → Maybe ℕ
        iterate zeros ones [] =
          just (if zeros <ᵇ ones then 1 else 0)
        iterate zeros ones (bitVec ∷ list) with eval bitVec
        ...                                   | just 0 = iterate (1 + zeros) ones list
        ...                                   | just 1 = iterate zeros (1 + ones) list
        ...                                   | _ = nothing

bitVecToℕ : {n : ℕ} → BitVec n → Maybe ℕ
bitVecToℕ [] = just 0
bitVecToℕ (0 ∷ v) = bitVecToℕ v
bitVecToℕ {n = suc n} (1 ∷ v) = maybeMap (λ k → 2 ^ n + k) (bitVecToℕ v)
bitVecToℕ (_ ∷ v) = nothing

invertBitVec : {n : ℕ} → BitVec n → BitVec n
invertBitVec [] = []
invertBitVec (0 ∷ v) = 1 ∷ invertBitVec v
invertBitVec (_ ∷ v) = 0 ∷ invertBitVec v

doTask : List (BitVec 12) → Maybe ℕ
doTask input = maybe*  gamma epsilon
               where
                 listMaybe : {k : ℕ} → Vec (Maybe ℕ) k → Maybe (Vec ℕ k)
                 listMaybe [] = just []
                 listMaybe (just x ∷ list) with listMaybe list
                 ...                          | just proccessedList = just (x ∷ proccessedList)
                 ...                          | nothing = nothing
                 listMaybe (nothing ∷ list) = nothing

                 maybeMaybe→Maybe : {A : Set} → Maybe (Maybe A) → Maybe A
                 maybeMaybe→Maybe (just (just x)) = just x
                 maybeMaybe→Maybe (just nothing) = nothing
                 maybeMaybe→Maybe nothing = nothing

                 maybe* : Maybe ℕ → Maybe ℕ → Maybe ℕ
                 maybe* (just x) (just y) = just (x * y)
                 maybe* (just x) nothing = nothing
                 maybe* nothing y = nothing

                 bitVecGamma = listMaybe (map (λ index → findMostCommonBit index input) (allFin 12))
                 gamma : Maybe ℕ
                 gamma = maybeMaybe→Maybe ((maybeMap bitVecToℕ) bitVecGamma)
                 epsilon = maybeMaybe→Maybe (maybeMap (bitVecToℕ ∘ invertBitVec) bitVecGamma)

main : IO ⊤
main = putStrLn (showMaybeNat (doTask input))


private
  -- checks from the exercise text
  testInput : List (BitVec 5)
  testInput =
    (0 ∷  0 ∷  1 ∷  0 ∷  0 ∷  []) ∷
    (1 ∷  1 ∷  1 ∷  1 ∷  0 ∷  []) ∷
    (1 ∷  0 ∷  1 ∷  1 ∷  0 ∷  []) ∷
    (1 ∷  0 ∷  1 ∷  1 ∷  1 ∷  []) ∷
    (1 ∷  0 ∷  1 ∷  0 ∷  1 ∷  []) ∷
    (0 ∷  1 ∷  1 ∷  1 ∷  1 ∷  []) ∷
    (0 ∷  0 ∷  1 ∷  1 ∷  1 ∷  []) ∷
    (1 ∷  1 ∷  1 ∷  0 ∷  0 ∷  []) ∷
    (1 ∷  0 ∷  0 ∷  0 ∷  0 ∷  []) ∷
    (1 ∷  1 ∷  0 ∷  0 ∷  1 ∷  []) ∷
    (0 ∷  0 ∷  0 ∷  1 ∷  0 ∷  []) ∷
    (0 ∷  1 ∷  0 ∷  1 ∷  0 ∷  []) ∷
    []

  _ : findMostCommonBit Fin.zero testInput ≡ just 1
  _ = refl

  _ : findMostCommonBit (Fin.suc Fin.zero) testInput ≡ just 0
  _ = refl

  _ : findMostCommonBit (Fin.suc (Fin.suc Fin.zero)) testInput ≡ just 1
  _ = refl

  _ : findMostCommonBit (Fin.suc (Fin.suc (Fin.suc Fin.zero))) testInput ≡ just 1
  _ = refl

  _ : findMostCommonBit (fromℕ 4) testInput ≡ just 0
  _ = refl

  -- test bitVecToℕ
  _ : bitVecToℕ (1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ []) ≡ just 22
  _ = refl
