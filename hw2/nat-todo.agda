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

-- Helper function for factorial-nonzero, to prove that iszero of a sum of numbers
-- is equivalent to the conjunction of iszero on each term in the sum.
iszero-+ : ∀ (n m : ℕ) → iszero (n + m) ≡ iszero n && iszero m
iszero-+ 0 0 = refl
iszero-+ 0 m = refl
iszero-+ (suc n) m rewrite iszero-+ n m = refl

-- 12 points
factorial-nonzero : ∀ (n : ℕ) → iszero (factorial n) ≡ ff
factorial-nonzero 0 = refl
factorial-nonzero (suc n) rewrite factorial-nonzero n | iszero-+ (factorial n) (n * factorial n) | factorial-nonzero n = refl

-- 12 points. hint: try induction on y 
pow+ : ∀ (x y z : ℕ) → x pow (y + z) ≡ (x pow y) * (x pow z)
pow+ x 0 z rewrite +0 (x pow z) = refl
pow+ x (suc y) z rewrite pow+ x y z | *assoc x (x pow y) (x pow z) = refl

-- 12 points
nonzero< : ∀ {n : ℕ} → (iszero n) ≡ ff → 0 < n ≡ tt
nonzero< {0} ()
nonzero< {suc x} p = refl

-- 12 points
parity-odd : ∀ (x : ℕ) → parity (x * 2 + 1) ≡ tt
parity-odd 0 = refl
parity-odd (suc x) rewrite parity-odd x = refl

-- 12 points
=ℕ-sym : ∀ (x y : ℕ) → (x =ℕ y) ≡ (y =ℕ x)
=ℕ-sym 0 0 = refl
=ℕ-sym 0 (suc y) = refl
=ℕ-sym (suc x) 0 = refl
=ℕ-sym (suc x) (suc y) rewrite =ℕ-sym x y = refl

-- another version of addition
_+'_ : ℕ → ℕ → ℕ
0 +' y = y
suc x +' y = x +' (suc y)

-- Helper function for parity-add, to prove that b xor ff ≡ b
xor-ff : ∀ (b : 𝔹) → b xor ff ≡ b
xor-ff ff = refl
xor-ff tt = refl

-- Helper function for parity-add, to prove that ff xor b ≡ b
ff-xor : ∀ (b : 𝔹) → ff xor b ≡ b
ff-xor ff = refl
ff-xor tt = refl

-- Helper function for parity-add, to prove that ~ (b1 xor b2) ≡ ~ b1 xor b2
~-xor : ∀ (b1 b2 : 𝔹) → ~ (b1 xor b2) ≡ ~ b1 xor b2
~-xor tt tt = refl
~-xor ff ff = refl
~-xor tt ff = refl
~-xor ff tt = refl

-- 13 points. x + y is odd (parity = tt) iff exactly one of x and y is odd
-- (either x is odd and y is even, or vice versa)
parity-add : ∀ (x y : ℕ) → parity (x + y) ≡ (parity x) xor (parity y)
parity-add 0 0 = refl
parity-add (suc x) 0 rewrite +0 x | xor-ff (~ parity x) = refl
parity-add 0 (suc y) rewrite ff-xor (~ parity y) = refl
parity-add (suc x) (suc y) rewrite parity-add x (suc y) | ~-xor (parity x) (~ parity y) = refl
