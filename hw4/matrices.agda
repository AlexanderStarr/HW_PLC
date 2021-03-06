module matrices where

open import lib

{- an n by m matrix consists of n rows, where each row is a vector of size m. -}
_by_matrix : ℕ → ℕ → Set
n by m matrix = 𝕍 (𝕍 ℕ m) n

{- 8 points.  The n by m zero matrix is just an n by m matrix where
   every element is 0.  Hint: this is very easy to write if you use
   the repeat𝕍 function from vector.agda -}
zero-matrix : (n m : ℕ) → n by m matrix
zero-matrix n m = repeat𝕍 (repeat𝕍 0 m) n

-- 2 points for passing this test case.
test-zero-matrix : zero-matrix 2 3 ≡ ((0 :: 0 :: 0 :: []) :: (0 :: 0 :: 0 :: []) :: [])
test-zero-matrix = refl

-- 0 points.  I suggest you write this function as a helper for matrix-to-string below.
row-to-string : ∀{m : ℕ} → 𝕍 ℕ m → string
row-to-string [] = ""
row-to-string (h :: []) = ℕ-to-string h
row-to-string (h :: t) =  ℕ-to-string h ^ " " ^ row-to-string t

{- 8 points.  Convert an n by m matrix to a string.  The format should
   be row1; row2; ...; rown, where each row looks like a1 a2 ... an.
   For an example, see test-matrix-to-string below -}
matrix-to-string : ∀ {n m : ℕ} → n by m matrix → string
matrix-to-string [] = ""
matrix-to-string (h :: []) = row-to-string h
matrix-to-string (h :: t) = row-to-string h ^ "; " ^ matrix-to-string t

-- 2 points for passing this test case.
test-matrix-to-string : matrix-to-string (zero-matrix 3 4) ≡ "0 0 0 0; 0 0 0 0; 0 0 0 0"
test-matrix-to-string = refl

{- 6 points. Return the i'th row of the matrix.  Hint: you can use the nth𝕍 function 
   from vector.agda -}
matrix-row : ∀{n m : ℕ}(i : ℕ) → i < n ≡ tt → n by m matrix → 𝕍 ℕ m
matrix-row i p mat = nth𝕍 i p mat

{- 7 points.  Get the element in row i, column j from the given n by m
   matrix, where i must be less than n and j less than m.  Hint: use
   matrix-row and nth𝕍. -}
matrix-elt : ∀{n m : ℕ}(i j : ℕ) → i < n ≡ tt → j < m ≡ tt → n by m matrix → ℕ
matrix-elt i j p q mat = nth𝕍 j q (matrix-row i p mat) 

{- 0 points. This is a helper for identity-matrixh below.
   
   diagonal-𝕍 d n k should return the vector of length n that
   has value d at index k and 0 for every other element -}
diagonal-𝕍 : (d n k : ℕ) → 𝕍 ℕ n
diagonal-𝕍 d 0 k = []
diagonal-𝕍 d (suc n) k with (n =ℕ k)
... | tt = d :: (diagonal-𝕍 d n k)
... | ff = 0 :: (diagonal-𝕍 d n k)

{- 0 points.  This is a helper for diagonal-matrix below.

   diagonal-matrixh should return the bottom m rows of the diagonal
   matrix with d along the diagonal -}
diagonal-matrixh : (d n m : ℕ) → m by n matrix
diagonal-matrixh d n 0 = []
diagonal-matrixh d n (suc m) = diagonal-𝕍 d n m :: diagonal-matrixh d n m

{- 12 points. This should return the n by n diagonal matrix (all
   elements 0 except that we have value d down the diagonal from top
   left to bottom right) -}
diagonal-matrix : (d : ℕ) → (n : ℕ) → n by n matrix
diagonal-matrix d n = diagonal-matrixh d n n

identity-matrix : (n : ℕ) → n by n matrix
identity-matrix n = diagonal-matrix 1 n

{- 3 points for passing this testcase, which shows what the 3 by 3
  identity matrix looks like: we have 1s down the diagonal and 0
  everywhere else -}
test-identity-matrix : identity-matrix 3 ≡ (1 :: 0 :: 0 :: []) :: 
                                           (0 :: 1 :: 0 :: []) :: 
                                           (0 :: 0 :: 1 :: []) :: []
test-identity-matrix = refl

n+1suc : ∀ (n : ℕ) → n + 1 ≡ suc n
n+1suc 0 = refl
n+1suc (suc n) rewrite n+1suc n = refl

init-𝕍-helper : ∀{ℓ}{A : Set ℓ}{m n : ℕ} → m < suc n ≡ tt → (f : (i : ℕ) → i < suc n ≡ tt → A) → 𝕍 A m
init-𝕍-helper {l} {A} {0} {n} p f = []
init-𝕍-helper {l} {A} {suc m} {n} p f rewrite sym (n+1suc m) with (<-suc-trans {m} {n} p)
... | p' = (init-𝕍-helper {l} {A} {m} {n} p' f) ++𝕍 [ f m p' ]𝕍

{- 10 points. Given a function f which takes an index i and a proof
   that i is less than n, return the vector of length n which looks
   like (f 0 p0) :: (f 1 p1) :: ... :: (f n-1 pn-1).  That is, the
   i'th element of the vector is (f i pi), where pi is the proof that
   i < n.  Hint: I found I had to write a helper function for this.
-}
init-𝕍 : ∀{ℓ}{A : Set ℓ}{n : ℕ} → (f : (i : ℕ) → i < n ≡ tt → A) → 𝕍 A n
init-𝕍 {l} {A} {0} f = []
init-𝕍 {l} {A} {suc n} f with (init-𝕍-helper {l} {A} {n} {n} (<-suc n) f) ++𝕍 [ f n (<-suc n) ]𝕍
... | r rewrite (n+1suc n) = r

{- 8 points: compute the dot product of two vectors v and u, in the sense
   of linear algebra: (v_0 * u_0) + ... + (v_k-1 * u_k-1), where 
   v_0 :: ... :: v_k-1 :: 0 and u_0 :: ... :: u_k-1 :: 0 are the 
   vectors v and u -}
_·_ : ∀{k : ℕ} → 𝕍 ℕ k → 𝕍 ℕ k → ℕ
[] · [] = 0
(x :: xs) · (y :: ys) = (x * y) + (xs · ys)

