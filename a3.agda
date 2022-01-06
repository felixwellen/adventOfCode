{-
  Day 3, 1st part
-}
module a3 where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String; primShowNat)
open import Agda.Builtin.Equality

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

data Bit : Set where
  one : Bit
  zero : Bit

BitVec = Vec Bit

Vecℕ→BitVec : {n : ℕ} → Vec ℕ n → Maybe (BitVec n)
Vecℕ→BitVec [] = just []
Vecℕ→BitVec (x ∷ v) with Vecℕ→BitVec v
...                     | just v' with x
...                                  | 0 = just (zero ∷ v')
...                                  | 1 = just (one ∷ v')
...                                  | suc (suc _) = nothing
Vecℕ→BitVec (x ∷ v)     | nothing = nothing

findMostCommonBit : {n : ℕ} (index : Fin n) → List (BitVec n) → Bit
findMostCommonBit {n = n} index input = iterate 0 0 input
  where
        iterate : (zeros : ℕ) (ones : ℕ) → List (BitVec n) → Bit
        iterate zeros ones [] =
          if zeros <ᵇ ones then one else zero
        iterate zeros ones (bitVec ∷ list) with lookup bitVec index
        ...                                   | zero = iterate (1 + zeros) ones list
        ...                                   | one = iterate zeros (1 + ones) list

bitVecToℕ : {n : ℕ} → BitVec n → ℕ
bitVecToℕ [] = 0
bitVecToℕ (zero ∷ v) = bitVecToℕ v
bitVecToℕ {n = suc n} (one ∷ v) = 2 ^ n + (bitVecToℕ v)

invertBitVec  : {n : ℕ} → BitVec n → BitVec n
invertBitVec  [] = []
invertBitVec  (zero ∷ v) = one ∷ invertBitVec v
invertBitVec  (one ∷ v) = zero ∷ invertBitVec v

listMaybe : {A : Set} → List (Maybe A) → Maybe (List A)
listMaybe [] = just []
listMaybe (just x ∷ list) with listMaybe list
...                          | just proccessedList = just (x ∷ proccessedList)
...                          | nothing = nothing
listMaybe (nothing ∷ list) = nothing

doTask : List (BitVec 12) → ℕ
doTask input = gamma * epsilon
               where
                 bitVecGamma = map (λ index → findMostCommonBit index input) (allFin 12)
                 gamma : ℕ
                 gamma = bitVecToℕ bitVecGamma
                 epsilon = bitVecToℕ (invertBitVec bitVecGamma)

main : IO ⊤
main = putStrLn (showMaybeNat ((maybeMap doTask) (listMaybe (mapList Vecℕ→BitVec input))))


private
  -- checks from the exercise text
  testInput : Maybe (List (BitVec 5))
  testInput = listMaybe (mapList Vecℕ→BitVec
    ((0 ∷  0 ∷  1 ∷  0 ∷  0 ∷  []) ∷
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
    []))

  _ : maybeMap (findMostCommonBit Fin.zero) testInput ≡ just one
  _ = refl

  _ : maybeMap (findMostCommonBit (Fin.suc Fin.zero)) testInput ≡ just zero
  _ = refl

  _ : maybeMap (findMostCommonBit (Fin.suc (Fin.suc Fin.zero))) testInput ≡ just one
  _ = refl

  _ : maybeMap (findMostCommonBit (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) testInput ≡ just one
  _ = refl

  _ : maybeMap (findMostCommonBit (fromℕ 4)) testInput ≡ just zero
  _ = refl

  -- test bitVecToℕ
  _ : bitVecToℕ (one ∷ zero ∷ one ∷ one ∷ zero ∷ []) ≡ 22
  _ = refl

  _ : Vecℕ→BitVec (1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ []) ≡ just (one ∷ zero ∷ one ∷ one ∷ zero ∷ [])
  _ = refl

  _ : Vecℕ→BitVec (1 ∷ 0 ∷ 1 ∷ 5 ∷ 0 ∷ []) ≡ nothing
  _ = refl
