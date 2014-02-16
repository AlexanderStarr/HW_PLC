module list-todo where

open import lib

-- 8 points
++[] : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A) → l ++ [] ≡ l
++[] = {!!}

-- 10 points
map-repeat : ∀ {ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(n : ℕ)(a : A)(f : A → B) → map f (repeat n a) ≡ repeat n (f a)
map-repeat = {!!}

-- 10 points
length-map : ∀{ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)(l : 𝕃 A) → length (map f l) ≡ length l
length-map = {!!}

-- 10 points
length-++ : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) → length (l1 ++ l2) ≡ (length l1) + (length l2)
length-++ = {!!}

-- 12 points (might not be that easy, because of reverse-helper)
reverse-++ : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) → reverse (l1 ++ l2) ≡ (reverse l2) ++ (reverse l1)
reverse-++ = {!!}

