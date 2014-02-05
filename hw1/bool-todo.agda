module bool-todo where

open import lib

infixr 4 _imp_ 

_imp_ : 𝔹 → 𝔹 → 𝔹
tt imp ff = ff 
b1 imp b2 = tt

ff-imp : ∀ (b : 𝔹) → ff imp b ≡ tt
ff-imp ff = refl
ff-imp tt = refl

imp-tt : ∀ (b : 𝔹) → b imp tt ≡ tt
imp-tt ff = refl
imp-tt tt = refl

imp-same : ∀ (b : 𝔹) → b imp b ≡ tt
imp-same ff = refl
imp-same tt = refl

&&-contra : ∀ (b : 𝔹) → b && ~ b ≡ ff
&&-contra = {!!}

&&-comm : ∀ (b1 b2 : 𝔹) → b1 && b2 ≡ b2 && b1
&&-comm = {!!}

||-comm : ∀ (b1 b2 : 𝔹) → b1 || b2 ≡ b2 || b1
||-comm = {!!}

&&-assoc : ∀ (b1 b2 b3 : 𝔹) → b1 && (b2 && b3) ≡ (b1 && b2) && b3
&&-assoc = {!!} 

||-assoc : ∀ (b1 b2 b3 : 𝔹) → b1 || (b2 || b3) ≡ (b1 || b2) || b3
||-assoc = {!!} 

~-over-&& : ∀ (b1 b2 : 𝔹) → ~ ( b1 && b2 ) ≡ (~ b1 || ~ b2)
~-over-&& = {!!}

~-over-|| : ∀ (b1 b2 : 𝔹) → ~ ( b1 || b2 ) ≡ (~ b1 && ~ b2)
~-over-|| = {!!}

&&-over-||-l : ∀ (a b c : 𝔹) → a && (b || c) ≡ (a && b) || (a && c)
&&-over-||-l = {!!}

&&-over-||-r : ∀ (a b c : 𝔹) → (a || b) && c ≡ (a && c) || (b && c)
&&-over-||-r = {!!}

||-over-&&-l : ∀ (a b c : 𝔹) → a || (b && c) ≡ (a || b) && (a || c)
||-over-&&-l = {!!}

||-over-&&-r : ∀ (a b c : 𝔹) → (a && b) || c ≡ (a || c) && (b || c)
||-over-&&-r = {!!}

imp-to-|| : ∀ (b1 b2 : 𝔹) → (b1 imp b2) ≡ (~ b1 || b2)
imp-to-|| = {!!}

imp-mp : ∀ {b b' : 𝔹} → b imp b' ≡ tt → b ≡ tt → b' ≡ tt
imp-mp = {!!}

&&-cong₁ : ∀ {b1 b1' b2 : 𝔹} → b1 ≡ b1' → b1 && b2 ≡ b1' && b2
&&-cong₁ = {!!}

&&-cong₂ : ∀ {b1 b2 b2' : 𝔹} → b2 ≡ b2' → b1 && b2 ≡ b1 && b2'
&&-cong₂ = {!!} 

~-cong : ∀ {b b' : 𝔹} → b ≡ b' → ~ b ≡ ~ b'
~-cong = {!!}

ite-cong₁ : ∀{ℓ}{A : Set ℓ} {b b' : 𝔹}(x y : A) → b ≡ b' → (if b then x else y) ≡ (if b' then x else y)
ite-cong₁ = {!!}

ite-cong₂ : ∀{ℓ}{A : Set ℓ} (b : 𝔹){x x' : A}(y : A) → x ≡ x' → (if b then x else y) ≡ (if b then x' else y)
ite-cong₂ = {!!}

ite-cong₃ : ∀{ℓ}{A : Set ℓ} (b : 𝔹)(x : A){y y' : A} → y ≡ y' → (if b then x else y) ≡ (if b then x else y')
ite-cong₃ = {!!}

&&-split : ∀ {b b' : 𝔹} → b || b' ≡ ff → b ≡ ff ⊎ b' ≡ ff
&&-split = {!!}

imp-ff : ∀ (b : 𝔹) → b imp ff ≡ ~ b
imp-ff = {!!}

tt-imp : ∀ (b : 𝔹) → tt imp b ≡ b
tt-imp = {!!}

