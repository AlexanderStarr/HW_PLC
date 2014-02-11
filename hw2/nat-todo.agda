module nat-todo where

open import lib

infixl 11 _pow_

-- 10 points to define x pow y so that it computes x to the power y.
-- So 2 pow 3 should equal 8, for example.
_pow_ : ℕ → ℕ → ℕ
x pow 0 = 1
x pow suc(y) = x * (x pow y)

-- 10 points.  The factorial of a number equals that number times all smaller numbers except 0.
-- So factorial 4 = 4 * 3 * 2 * 1 = 24.
factorial : ℕ → ℕ
factorial 0 = 1
factorial (suc x) = (suc x) * factorial (x)

-- 12 points
*1 : ∀ {n : ℕ} → n * 1 ≡ n
*1 {n} rewrite *comm n 1 | +0 n = refl

-- 12 points
1-pow : ∀ {n : ℕ} → 1 pow n ≡ 1
1-pow {0} = refl
1-pow {suc n} rewrite 1-pow {n} | +0 n = refl

iszero-assoc : ∀ (n m : ℕ) → iszero (n + m) ≡ iszero n && iszero m
iszero-assoc 0 0 = refl
iszero-assoc 0 m = refl
iszero-assoc (suc n) m rewrite iszero-assoc n m = refl

-- 12 points
factorial-nonzero : ∀ (n : ℕ) → iszero (factorial n) ≡ ff
factorial-nonzero 0 = refl
factorial-nonzero (suc n) rewrite factorial-nonzero n | iszero-assoc (factorial n) (n * factorial n) = {!!}

-- 12 points. hint: try induction on y 
pow+ : ∀ (x y z : ℕ) → x pow (y + z) ≡ (x pow y) * (x pow z)
pow+ x 0 z rewrite +0 (x pow z) = refl
pow+ x (suc y) z rewrite pow+ x y z | *assoc x (x pow y) (x pow z) = refl

-- 12 points
nonzero< : ∀ {n : ℕ} → (iszero n) ≡ ff → 0 < n ≡ tt
nonzero< {0} = sym
nonzero< {suc x} = {!!}

-- 12 points
parity-odd : ∀ (x : ℕ) → parity (x * 2 + 1) ≡ tt
parity-odd 0 = refl
parity-odd (suc x) rewrite parity-odd x = refl

-- 12 points
=ℕ-sym : ∀ (x y : ℕ) → (x =ℕ y) ≡ (y =ℕ x)
=ℕ-sym x y = {!!}

-- another version of addition
_+'_ : ℕ → ℕ → ℕ
0 +' y = y
suc x +' y = x +' (suc y)

-- 12 points. You are not allowed to call +comm when proving this one
-- (though you can certainly borrow ideas from the code for +comm):
+'comm : ∀ (x y : ℕ) → x +' y ≡ y +' x
+'comm = {!!}

-- 12 points
+'-equiv-+ : ∀ (x y : ℕ) → x + y ≡ x +' y
+'-equiv-+ = {!!}

-- 12 points
+inj1 : ∀ {x y z : ℕ} → x + y ≡ x + z → y ≡ z
+inj1 = {!!}

-- 12 points
+inj2 : ∀ {x y z : ℕ} → x + z ≡ y + z → x ≡ y
+inj2 = {!!}

-- 12 points
*distribl : ∀ (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
*distribl = {!!}

-- 12 points
pow* : ∀ (x y z : ℕ) → x pow (y * z) ≡ (x pow y) pow z
pow* = {!!}

-- 12 points
*inj1 : ∀ {x y z : ℕ} → x ≢ 0 → x * y ≡ x * z → y ≡ z
*inj1 = {!!}

-- 12 points
*inj2 : ∀ {x y z : ℕ} → z ≢ 0 → x * z ≡ y * z → x ≡ y
*inj2 = {!!}

-- 13 points
factorial-mono : ∀ (x y : ℕ) → 0 < x ≡ tt → x < y ≡ tt → factorial x < factorial y ≡ tt
factorial-mono = {!!}

-- 13 points. x + y is odd (parity = tt) iff exactly one of x and y is odd
-- (either x is odd and y is even, or vice versa)
parity-add : ∀ (x y : ℕ) → parity (x + y) ≡ (parity x) xor (parity y)
parity-add = {!!}

-- 13 points. x * y is odd (parity = tt) iff x is odd and y is odd.
parity-mult : ∀ (x y : ℕ) → parity (x * y) ≡ (parity x) && (parity y)
parity-mult = {!!}

-- 15 points. [probably hard] this might require case-splitting on whether or not x > z
+∸ : ∀ (x y z : ℕ) → (x + y) ∸ z ≡ (x ∸ z) + (y ∸ (z ∸ x))
+∸ = {!!}

