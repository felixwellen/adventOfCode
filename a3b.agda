{-
  Day 3, 2nd part
-}
module a3b where

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

bitVecToℕ : {n : ℕ} → BitVec n → ℕ
bitVecToℕ [] = 0
bitVecToℕ (zero ∷ v) = bitVecToℕ v
bitVecToℕ {n = suc n} (one ∷ v) = 2 ^ n + (bitVecToℕ v)

listMaybe : {A : Set} → List (Maybe A) → Maybe (List A)
listMaybe [] = just []
listMaybe (just x ∷ list) with listMaybe list
...                          | just proccessedList = just (x ∷ proccessedList)
...                          | nothing = nothing
listMaybe (nothing ∷ list) = nothing

module _ {n : ℕ} (index : Fin n) (input : List (BitVec n)) where
  private
    iterate : (pick : (zeros : ℕ) → (ones : ℕ) → Bit) (zeros : ℕ) (ones : ℕ) → List (BitVec n) → Bit
    iterate pick zeros ones [] = pick zeros ones
    iterate pick zeros ones (bitVec ∷ list) with lookup bitVec index
    ...                                   | zero = iterate pick (1 + zeros) ones list
    ...                                   | one = iterate pick zeros (1 + ones) list

  mostCommonBit :  Bit
  mostCommonBit = iterate (λ zeros ones → if ones <ᵇ zeros then zero else one) 0 0 input

  leastCommonBit : Bit
  leastCommonBit = iterate (λ zeros ones → if zeros <ᵇ ones then one else zero) 0 0 input

doTask : List (BitVec 12) → ℕ
doTask input = ?

containsMoreThanOne : {A : Set} → List A → Bool
containsMoreThanOne [] = false
containsMoreThanOne (x ∷ []) = false
containsMoreThanOne (x ∷ y ∷ _) = true

main : IO ⊤
main = putStrLn (showMaybeNat ((maybeMap doTask) (listMaybe (mapList Vecℕ→BitVec input))))


private
  -- tests from the exercise text
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

  _ : maybeMap (mostCommonBit Fin.zero) testInput ≡ just one
  _ = refl

  _ : maybeMap (mostCommonBit (Fin.suc Fin.zero)) testInput ≡ just zero
  _ = refl

  _ : maybeMap (mostCommonBit (Fin.suc (Fin.suc Fin.zero))) testInput ≡ just one
  _ = refl

  _ : maybeMap (mostCommonBit (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) testInput ≡ just one
  _ = refl

  _ : maybeMap (mostCommonBit (fromℕ 4)) testInput ≡ just zero
  _ = refl

  -- test for part two
  _ : mostCommonBit Fin.zero ((one ∷ zero ∷ []) ∷ (zero ∷ zero ∷ []) ∷ [])  ≡ one
  _ = refl

  _ : leastCommonBit Fin.zero ((one ∷ zero ∷ []) ∷ (zero ∷ zero ∷ []) ∷ [])  ≡ zero
  _ = refl

  -- test bitVecToℕ
  _ : bitVecToℕ (one ∷ zero ∷ one ∷ one ∷ zero ∷ []) ≡ 22
  _ = refl

  _ : Vecℕ→BitVec (1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ []) ≡ just (one ∷ zero ∷ one ∷ one ∷ zero ∷ [])
  _ = refl

  _ : Vecℕ→BitVec (1 ∷ 0 ∷ 1 ∷ 5 ∷ 0 ∷ []) ≡ nothing
  _ = refl
