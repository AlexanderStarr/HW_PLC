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

----------------------------------------------------------------------
-- one new one about vectors
----------------------------------------------------------------------


