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
&&-contra ff = refl
&&-contra tt = refl

&&-comm : ∀ (b1 b2 : 𝔹) → b1 && b2 ≡ b2 && b1
&&-comm ff ff = refl
&&-comm ff tt = refl
&&-comm tt ff = refl
&&-comm tt tt = refl

||-comm : ∀ (b1 b2 : 𝔹) → b1 || b2 ≡ b2 || b1
||-comm ff ff = refl
||-comm ff tt = refl
||-comm tt ff = refl
||-comm tt tt = refl

&&-assoc : ∀ (b1 b2 b3 : 𝔹) → b1 && (b2 && b3) ≡ (b1 && b2) && b3
&&-assoc ff b1 b2 = refl
&&-assoc tt b1 b2 rewrite &&-comm b1 b2 = refl

||-assoc : ∀ (b1 b2 b3 : 𝔹) → b1 || (b2 || b3) ≡ (b1 || b2) || b3
||-assoc tt b1 b2 = refl
||-assoc ff b1 b2 rewrite ||-comm b1 b2 = refl

~-over-&& : ∀ (b1 b2 : 𝔹) → ~ ( b1 && b2 ) ≡ (~ b1 || ~ b2)
~-over-&& ff ff = refl
~-over-&& ff tt = refl
~-over-&& tt ff = refl
~-over-&& tt tt = refl

~-over-|| : ∀ (b1 b2 : 𝔹) → ~ ( b1 || b2 ) ≡ (~ b1 && ~ b2)
~-over-|| ff ff = refl
~-over-|| ff tt = refl
~-over-|| tt ff = refl
~-over-|| tt tt = refl

&&-over-||-l : ∀ (a b c : 𝔹) → a && (b || c) ≡ (a && b) || (a && c)
&&-over-||-l ff b1 b2 = refl
&&-over-||-l tt tt b = refl
&&-over-||-l tt ff ff = refl
&&-over-||-l tt ff tt = refl

&&-over-||-r : ∀ (a b c : 𝔹) → (a || b) && c ≡ (a && c) || (b && c)
&&-over-||-r ff ff b = refl
&&-over-||-r ff tt ff = refl
&&-over-||-r tt ff ff = refl
&&-over-||-r tt tt ff = refl
&&-over-||-r tt ff tt = refl
&&-over-||-r ff tt tt = refl
&&-over-||-r tt tt tt = refl

||-over-&&-l : ∀ (a b c : 𝔹) → a || (b && c) ≡ (a || b) && (a || c)
||-over-&&-l tt b1 b2 = refl
||-over-&&-l ff ff b2 = refl
||-over-&&-l ff tt ff = refl
||-over-&&-l ff tt tt = refl

||-over-&&-r : ∀ (a b c : 𝔹) → (a && b) || c ≡ (a || c) && (b || c)
||-over-&&-r ff b ff = refl
||-over-&&-r tt ff ff = refl
||-over-&&-r ff ff tt = refl
||-over-&&-r tt tt b = refl
||-over-&&-r tt ff tt = refl
||-over-&&-r ff tt tt = refl

imp-to-|| : ∀ (b1 b2 : 𝔹) → (b1 imp b2) ≡ (~ b1 || b2)
imp-to-|| ff ff = refl
imp-to-|| ff tt = refl
imp-to-|| tt ff = refl
imp-to-|| tt tt = refl

imp-mp : ∀ {b b' : 𝔹} → b imp b' ≡ tt → b ≡ tt → b' ≡ tt
imp-mp = {!!}

&&-cong₁ : ∀ {b1 b1' b2 : 𝔹} → b1 ≡ b1' → b1 && b2 ≡ b1' && b2
&&-cong₁ = ?

&&-cong₂ : ∀ {b1 b2 b2' : 𝔹} → b2 ≡ b2' → b1 && b2 ≡ b1 && b2'
&&-cong₂ = {!!} 

~-cong : ∀ {b b' : 𝔹} → b ≡ b' → ~ b ≡ ~ b'
~-cong = {!!}

ite-cong₁ : ∀{ℓ}{A : Set ℓ} {b b' : 𝔹}(x y : A) → b ≡ b' → (if b then x else y) ≡ (if b' then x else y)
ite-cong₁ = {!!}

ite-cong₂ : ∀{ℓ}{A : Set ℓ} (b : 𝔹){x x' : A}(y : A) → x ≡ x' → (if b then x else y) ≡ (if b then x' else y)
ite-cong₂ = {!!}

ite-cong₃ : ∀{ℓ}{A : Set ℓ} (b : 𝔹)(x : A){y y' : A} → y ≡ y' → (if b then x else y) ≡ (if b then x else y')
ite-cong₃ tt x y = refl
ite-cong₃ ff x y = {!!}

&&-split : ∀ {b b' : 𝔹} → b || b' ≡ ff → b ≡ ff ⊎ b' ≡ ff
&&-split = {!!}

imp-ff : ∀ (b : 𝔹) → b imp ff ≡ ~ b
imp-ff ff = refl
imp-ff tt = refl

tt-imp : ∀ (b : 𝔹) → tt imp b ≡ b
tt-imp ff = refl
tt-imp tt = refl

