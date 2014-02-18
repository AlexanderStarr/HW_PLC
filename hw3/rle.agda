module rle where

open import lib

data run : Set where
  nonempty-run : 𝔹 → ℕ → (𝕃 ℕ) → run
  empty-run : run

-- 10 points
decode : run → 𝕃 𝔹
decode empty-run = []
decode (nonempty-run b n []) = repeat (n + 1) b
decode (nonempty-run b n (nl :: l)) = ((repeat (n + 1) b) ++ (decode (nonempty-run (~ b) nl l)))

test-input = ff :: tt :: tt :: tt :: ff :: ff :: []

decode-test1 = decode (nonempty-run ff 0 (2 :: 1 :: []))

-- 3 points for passing this test
-- If decode works properly, this should evaluate to refl.
lem-decode-test1 : decode-test1 ≡ test-input
lem-decode-test1 = refl

-- 1 point for passing this test
lem-decode-empty : decode empty-run ≡ []
lem-decode-empty = refl

{- 0 points: this is just a helper for encode.

   Given a boolean b and a run encoding a list of booleans bs,
   construct a new run that encodes the list of booleans b :: bs.

   See encodeh-lem1, encodeh-lem2, and encodeh-lem3 for 
   properties this should satisfy.

   You are not required to define encode using encodeh, but
   I found it much easier to do it this way than the alternatives
   I considered.
-}
encodeh : 𝔹 → run → run
encodeh b empty-run = (nonempty-run b 0 [])
encodeh b (nonempty-run bs n l) = if (~ (b xor bs)) then (nonempty-run b (suc n) l) else (nonempty-run b 0 (n :: l))

-- 10 points.  Hint: use encodeh in the case where the list is of the form (b :: bs).
encode : 𝕃 𝔹 → run
encode [] = empty-run
encode (b :: bs) = encodeh b (encode bs)

encode-test1 = encode test-input

-- 3 points for passing this test case
lem-encode-test1 : encode-test1 ≡ nonempty-run ff 0 (2 :: 1 :: [])
lem-encode-test1 = refl

-- 1 points for this test case
lem-encode-empty : encode [] ≡ empty-run 
lem-encode-empty = refl

-- 3 points.  I found this and the next two lemmas useful for encode-decode and decode-encode below
encodeh-lem : ∀ (b : 𝔹) → encodeh b empty-run ≡ nonempty-run b 0 []
encodeh-lem ff = refl
encodeh-lem tt = refl

-- 3 points.  
encodeh-lem2 : ∀ (b : 𝔹) (n : ℕ) (ns : 𝕃 ℕ) → encodeh b (nonempty-run (~ b) n ns) ≡ nonempty-run b 0 (n :: ns)
encodeh-lem2 ff n ns = refl
encodeh-lem2 tt n ns = refl

-- 3 points.  
encodeh-lem3 : ∀ (b : 𝔹)(n : ℕ)(ns : 𝕃 ℕ) → encodeh b (nonempty-run b n ns) ≡ nonempty-run b (suc n) ns
encodeh-lem3 ff n ns = refl
encodeh-lem3 tt n ns = refl

-- 10 points (I found I needed this for decode-length below)
decode-length-neg : ∀ (b : 𝔹) (n : ℕ) (ns : 𝕃 ℕ) → length (decode (nonempty-run b n ns)) ≡ length (decode (nonempty-run (~ b) n ns))
decode-length-neg b 0 [] = refl
decode-length-neg b (suc n) [] rewrite decode-length-neg b n [] = refl
decode-length-neg b 0 (nn :: ns) rewrite decode-length-neg (~ b) nn ns = refl
decode-length-neg b (suc n) (nn :: ns) rewrite decode-length-neg b n (nn :: ns) | decode-length-neg (~ b) nn ns = refl

-- 12 points (not needed for encode-decode or decode-encode theorems below
decode-length : ∀ (b : 𝔹) (n : ℕ) (ns : 𝕃 ℕ) → suc (length ns) ≤ length (decode (nonempty-run b n ns)) ≡ tt
decode-length b 0 [] = refl
decode-length b (suc n) [] rewrite decode-length b n [] = {!!}
decode-length b 0 (nn :: ns) = {!!}
decode-length b (suc n) (nn :: ns) = {!!}

-- Helper function for encode-repeat
xor-same : ∀ (b : 𝔹) → b xor b ≡ ff
xor-same ff = refl
xor-same tt = refl

-- 12 points
encode-repeat : ∀ (b : 𝔹)(n : ℕ) → encode (repeat (suc n) b) ≡ (nonempty-run b n [])
encode-repeat b 0 = refl
encode-repeat b (suc n) rewrite encode-repeat b n | xor-same b = refl

-- 8 points
decode-encodeh : ∀ (b : 𝔹) (r : run) → decode (encodeh b r) ≡ b :: decode r
decode-encodeh b empty-run = refl
decode-encodeh b r = {!!}

-- 15 points
decode-encode : ∀ (l : 𝕃 𝔹) → decode (encode l) ≡ l
decode-encode = {!!}

-- 15 points
encode-decode : ∀ (r : run) → encode (decode r) ≡ r
encode-decode = {!!}
