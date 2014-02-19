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

-- Helper lemma for reverse-++.
lem-reverse++ : ∀{ℓ}{A : Set ℓ}(e : A)(l1 l2 l3 : 𝕃 A) → reverse-helper (e :: []) l1 ++ reverse-helper l2 l3 ≡ reverse-helper l2 (l3 ++ e :: l1)
lem-reverse++ e l1 [] [] rewrite ++[] (reverse-helper (e :: []) l1) = refl
lem-reverse++ e l1 [] (h :: l3) rewrite lem-reverse++ e l1 (h :: []) l3 = refl
lem-reverse++ e l1 (h :: l2) [] = {!!}
lem-reverse++ e l1 (h2 :: l2) (h3 :: l3) = {!!}

-- 12 points (might not be that easy, because of reverse-helper)
reverse-++ : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) → reverse (l1 ++ l2) ≡ (reverse l2) ++ (reverse l1)
reverse-++ l1 [] rewrite ++[] l1 = refl
reverse-++ l1 (e2 :: l2) rewrite reverse-++ l1 l2 | lem-reverse++ e2 l2 [] l1 = refl
