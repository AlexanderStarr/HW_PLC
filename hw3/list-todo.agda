module list-todo where

open import lib

-- 8 points
++[] : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A) → l ++ [] ≡ l
++[] [] = refl
++[] (e :: l) rewrite ++[] l = refl

-- 10 points
map-repeat : ∀ {ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(n : ℕ)(a : A)(f : A → B) → map f (repeat n a) ≡ repeat n (f a)
map-repeat 0 a f = refl
map-repeat (suc n) a f rewrite map-repeat n a f = refl

-- 10 points
length-map : ∀{ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)(l : 𝕃 A) → length (map f l) ≡ length l
length-map f [] = refl
length-map f (e :: l) rewrite length-map f l = refl

-- 10 points
length-++ : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) → length (l1 ++ l2) ≡ (length l1) + (length l2)
length-++ [] l2 = refl
length-++ (e :: l1) l2 rewrite length-++ l1 l2 = refl

