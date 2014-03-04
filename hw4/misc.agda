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
+perm3 w x y z rewrite +assoc (w + x) y z | +comm w y | +comm (w + x) y | +assoc y w x | +assoc (y + w) x z = refl

-- 5 points
parity-pow2 : ∀ (y : ℕ) → iszero y ≡ ff → parity (2 pow y) ≡ ff
parity-pow2 0 p = p
parity-pow2 (suc 0) p = refl
parity-pow2 (suc y) p rewrite parity-add (2 pow y) (2 pow y + 0) | +0 (2 pow y) | xor-same {parity (2 pow y)} = refl

----------------------------------------------------------------------
-- similar to hw3
----------------------------------------------------------------------

-- 5 points
::++ : ∀{ℓ}{A : Set ℓ}(a : A)(l1 l2 : 𝕃 A) → a :: (l1 ++ l2) ≡ (a :: l1) ++ l2
::++ a l1 l2 = refl

-- 5 points
repeat-++ : ∀{ℓ}{A : Set ℓ} (n m : ℕ) (a : A) → (repeat n a) ++ (repeat m a) ≡ repeat (n + m) a
repeat-++ 0 m a = refl
repeat-++ (suc n) m a rewrite repeat-++ n m a = refl

map-reverse-h : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(l1 l2 : 𝕃 A)(f : A → B) → map f (reverse-helper l1 l2) ≡ reverse-helper (map f l1) (map f l2)
map-reverse-h l1 [] f = refl
map-reverse-h l1 (h2 :: t2) f rewrite map-reverse-h (h2 :: l1) t2 f = refl

-- 5 points
map-reverse : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(l : 𝕃 A)(f : A → B) → map f (reverse l) ≡ reverse (map f l)
map-reverse [] f = refl
map-reverse (h :: t) f rewrite map-reverse-h (h :: []) t f = refl

----------------------------------------------------------------------
-- one new one about vectors
----------------------------------------------------------------------

𝕍+suc : ∀ {ℓ}{A : Set ℓ}(n m : ℕ) → 𝕍 A (m + suc n) ≡ 𝕍 A (suc (m + n))
𝕍+suc n m rewrite +suc m n = refl

-- Helper function for reverse𝕍
reverse𝕍-helper : ∀ {ℓ}{A : Set ℓ}{n m : ℕ} → 𝕍 A n → 𝕍 A m → 𝕍 A (n + m)
reverse𝕍-helper {l} {A} {n} {0} h [] rewrite +0 n = h
reverse𝕍-helper {l} {A} {n} {suc m} h (x :: xs) rewrite +suc n m = reverse𝕍-helper (x :: h) xs

{- 10 points. This function should reverse a vector,
   similarly to the way the reverse function in list.agda
   reverses a list-}
reverse𝕍 : ∀{ℓ}{A : Set ℓ}{n : ℕ} → 𝕍 A n → 𝕍 A n
reverse𝕍 {l} {A} {n} v = reverse𝕍-helper [] v

-- 0 points.  This is a testcase for reverse𝕍
reverse𝕍-test : reverse𝕍 (1 :: 2 :: 3 :: []) ≡ 3 :: 2 :: 1 :: []
reverse𝕍-test = refl

