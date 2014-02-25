module misc where

open import lib

----------------------------------------------------------------------
-- similar to hw1 
----------------------------------------------------------------------

-- 3 points
xor-same : ∀ {b : 𝔹} → b xor b ≡ ff
xor-same {tt} = refl
xor-same {ff} = refl

-- 3 points
xor-comm : ∀ {b1 b2 : 𝔹} → b1 xor b2 ≡ b2 xor b1
xor-comm {tt} {tt} = refl
xor-comm {tt} {ff} = refl
xor-comm {ff} {tt} = refl
xor-comm {ff} {ff} = refl

----------------------------------------------------------------------
-- similar to hw2
----------------------------------------------------------------------

-- 4 points
+perm3 : ∀ (w x y z : ℕ) → (w + x) + (y + z) ≡ (w + y) + (x + z)
+perm3 w x y z = {!!}

-- 5 points
parity-pow : ∀ (x y : ℕ) → iszero y ≡ ff → parity (x pow y) ≡ parity x
parity-pow x 0 ()
parity-pow x (suc 0) p rewrite *comm x 1 | +0 x = refl
parity-pow x (suc y) p = {!!}

-- 7 points (no one got this on hw2)
*inj1 : ∀ {x y z : ℕ} → x ≢ 0 → x * y ≡ x * z → y ≡ z
*inj1 = {!!}

-- 7 points (no one got this on hw2)
*inj2 : ∀ {x y z : ℕ} → z ≢ 0 → x * z ≡ y * z → x ≡ y
*inj2 = {!!}

-- 8 points (no one got this on hw2)
+∸ : ∀ (x y z : ℕ) → (x + y) ∸ z ≡ (x ∸ z) + (y ∸ (z ∸ x))
+∸ = {!!}

----------------------------------------------------------------------
-- similar to hw3
----------------------------------------------------------------------

-- 5 points
::++ : ∀{ℓ}{A : Set ℓ}(a : A)(l1 l2 : 𝕃 A) → a :: (l1 ++ l2) ≡ (a :: l1) ++ l2
::++ = {!!}

-- 5 points
repeat-++ : ∀{ℓ}{A : Set ℓ} (n m : ℕ) (a : A) → (repeat n a) ++ (repeat m a) ≡ repeat (n + m) a
repeat-++ = {!!}

-- 5 points
++-≡-[] : ∀{ℓ}{A : Set ℓ}{l1 l2 : 𝕃 A} → l1 ++ l2 ≡ [] → l1 ≡ [] ∧ l2 ≡ []
++-≡-[] = {!!}

-- 5 points
map-reverse : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(l : 𝕃 A)(f : A → B) → map f (reverse l) ≡ reverse (map f l)
map-reverse = {!!}

----------------------------------------------------------------------
-- one new one about vectors
----------------------------------------------------------------------

{- 10 points. This function should reverse a vector,
   similarly to the way the reverse function in list.agda
   reverses a list -}
reverse𝕍 : ∀{ℓ}{A : Set ℓ}{n : ℕ} → 𝕍 A n → 𝕍 A n
reverse𝕍 = {!!}

-- 0 points.  This is a testcase for reverse𝕍
reverse𝕍-test : reverse𝕍 (1 :: 2 :: 3 :: []) ≡ 3 :: 2 :: 1 :: []
reverse𝕍-test = {!!}
{-
reverse-𝕍-helper : ∀ {ℓ}{A : Set ℓ}{n m : ℕ} → 𝕍 A n → 𝕍 A m → 𝕍 A m
reverse-𝕍-helper h [] = h
reverse-𝕍-helper h (x :: xs) = reverse-𝕍-helper (x :: h) xs

reverse-𝕍 : ∀ {ℓ}{A : Set ℓ}{n : ℕ} → 𝕍 A n → 𝕍 A n
reverse-𝕍 v = reverse-helper [] v-}
