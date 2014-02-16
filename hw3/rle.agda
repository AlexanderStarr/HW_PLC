module rle where

open import lib

data run : Set where
  nonempty-run : 𝔹 → ℕ → (𝕃 ℕ) → run
  empty-run : run

-- 10 points
decode : run → 𝕃 𝔹
decode = {!!}

test-input = ff :: tt :: tt :: tt :: ff :: ff :: []

decode-test1 = decode (nonempty-run ff 0 (2 :: 1 :: []))

-- 3 points for passing this test
lem-decode-test1 : decode-test1 ≡ test-input
lem-decode-test1 = {!!}

-- 1 point for passing this test
lem-decode-empty : decode empty-run ≡ []
lem-decode-empty = {!!}

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
encodeh = {!!}

-- 10 points.  Hint: use encodeh in the case where the list is of the form (b :: bs).
encode : 𝕃 𝔹 → run
encode = {!!}

encode-test1 = encode test-input

-- 3 points for passing this test case
lem-encode-test1 : encode-test1 ≡ nonempty-run ff 0 (2 :: 1 :: [])
lem-encode-test1 = {!!}

-- 1 points for this test case
lem-encode-empty : encode [] ≡ empty-run 
lem-encode-empty = {!!}

-- 3 points.  I found this and the next two lemmas useful for encode-decode and decode-encode below
encodeh-lem : ∀ (b : 𝔹) → encodeh b empty-run ≡ nonempty-run b 0 []
encodeh-lem = {!!}

-- 3 points.  
encodeh-lem2 : ∀ (b : 𝔹) (n : ℕ) (ns : 𝕃 ℕ) → encodeh b (nonempty-run (~ b) n ns) ≡ nonempty-run b 0 (n :: ns)
encodeh-lem2 = {!!}

-- 3 points.  
encodeh-lem3 : ∀ (b : 𝔹)(n : ℕ)(ns : 𝕃 ℕ) → encodeh b (nonempty-run b n ns) ≡ nonempty-run b (suc n) ns
encodeh-lem3 = {!!}

-- 10 points (I found I needed this for decode-length below)
decode-length-neg : ∀ (b : 𝔹) (n : ℕ) (ns : 𝕃 ℕ) → length (decode (nonempty-run b n ns)) ≡ length (decode (nonempty-run (~ b) n ns))
decode-length-neg = {!!}

-- 12 points (not needed for encode-decode or decode-encode theorems below
decode-length : ∀ (b : 𝔹) (n : ℕ) (ns : 𝕃 ℕ) → suc (length ns) ≤ length (decode (nonempty-run b n ns)) ≡ tt
decode-length = {!!}

-- 12 points
encode-repeat : ∀ (b : 𝔹)(n : ℕ) → encode (repeat (suc n) b) ≡ (nonempty-run b n [])
encode-repeat = {!!}

-- 8 points
decode-encodeh : ∀ (b : 𝔹) (r : run) → decode (encodeh b r) ≡ b :: decode r
decode-encodeh = {!!}

-- 15 points
decode-encode : ∀ (l : 𝕃 𝔹) → decode (encode l) ≡ l
decode-encode = {!!}

-- 15 points
encode-decode : ∀ (r : run) → encode (decode r) ≡ r
encode-decode = {!!}
