module rle where

open import lib

data run : Set where
  nonempty-run : 𝔹 → ℕ → (𝕃 ℕ) → run
  empty-run : run

{- for benefit of mac users, who cannot see the blackboard fonts,
   I have put some definitions with names like mac-XXXX to show the 
   types -}
mac-nonempty-run : bool → nat → list nat → run
mac-nonempty-run = nonempty-run

-- 10 points
decode : run → 𝕃 𝔹
decode empty-run = []
decode (nonempty-run b n []) = repeat (suc n) b
decode (nonempty-run b n (nl :: l)) = ((repeat (suc n) b) ++ (decode (nonempty-run (~ b) nl l)))

mac-decode : run → list bool
mac-decode = decode

test-input : 𝕃 𝔹
test-input = ff :: tt :: tt :: tt :: ff :: ff :: []

mac-test-input : list bool
mac-test-input = test-input

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
encodeh ff (nonempty-run ff n l) = (nonempty-run ff (suc n) l)
encodeh ff (nonempty-run tt n l) = (nonempty-run ff 0 (n :: l))
encodeh tt (nonempty-run ff n l) = (nonempty-run tt 0 (n :: l)) 
encodeh tt (nonempty-run tt n l) = (nonempty-run tt (suc n) l)

-- Could do it this way, but it might be better to flatten it out, and match on all possible casses for b and bs.
--encodeh b (nonempty-run bs n l) = if (~ (b xor bs)) then (nonempty-run b (suc n) l) else (nonempty-run b 0 (n :: l))

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
encodeh-lem b = refl

mac-encodeh-lem : ∀ (b : bool) → encodeh b empty-run ≡ nonempty-run b 0 []
mac-encodeh-lem = encodeh-lem

-- 3 points.  
encodeh-lem2 : ∀ (b : 𝔹) (n : ℕ) (ns : 𝕃 ℕ) → encodeh b (nonempty-run (~ b) n ns) ≡ nonempty-run b 0 (n :: ns)
encodeh-lem2 ff n ns = refl
encodeh-lem2 tt n ns = refl

mac-encodeh-lem2 : ∀ (b : 𝔹) (n : ℕ) (ns : 𝕃 ℕ) → encodeh b (nonempty-run (~ b) n ns) ≡ nonempty-run b 0 (n :: ns)
mac-encodeh-lem2 = encodeh-lem2

-- 3 points.  
encodeh-lem3 : ∀ (b : 𝔹)(n : ℕ)(ns : 𝕃 ℕ) → encodeh b (nonempty-run b n ns) ≡ nonempty-run b (suc n) ns
encodeh-lem3 ff n ns = refl
encodeh-lem3 tt n ns = refl

mac-encodeh-lem3 : ∀ (b : bool)(n : nat)(ns : list nat) → encodeh b (nonempty-run b n ns) ≡ nonempty-run b (suc n) ns
mac-encodeh-lem3 = encodeh-lem3

-- 10 points (I found I needed this for decode-length below)
decode-length-neg : ∀ (b : 𝔹) (n : ℕ) (ns : 𝕃 ℕ) → length (decode (nonempty-run b n ns)) ≡ length (decode (nonempty-run (~ b) n ns))
decode-length-neg b 0 [] = refl
decode-length-neg b (suc n) [] rewrite decode-length-neg b n [] = refl
decode-length-neg b 0 (nn :: ns) rewrite decode-length-neg (~ b) nn ns = refl
decode-length-neg b (suc n) (nn :: ns) rewrite decode-length-neg b n (nn :: ns) | decode-length-neg (~ b) nn ns = refl

mac-decode-length-neg : ∀ (b : bool) (n : nat) (ns : list nat) → length (decode (nonempty-run b n ns)) ≡ length (decode (nonempty-run (~ b) n ns))
mac-decode-length-neg = decode-length-neg

length-++ : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) → length (l1 ++ l2) ≡ (length l1) + (length l2)
length-++ [] l2 = refl
length-++ (e :: l1) l2 rewrite length-++ l1 l2 = refl

-- 12 points
encode-repeat : ∀ (b : 𝔹)(n : ℕ) → encode (repeat (suc n) b) ≡ (nonempty-run b n [])
encode-repeat b 0 = refl
encode-repeat b (suc n) rewrite encode-repeat b n | encodeh-lem3 b n [] = refl

mac-encode-repeat : ∀ (b : bool)(n : nat) → encode (repeat (suc n) b) ≡ (nonempty-run b n [])
mac-encode-repeat = encode-repeat

-- Helper function for decode-encodeh
deh-helper : ∀ (b : 𝔹)(n : ℕ)(l : 𝕃 ℕ) → decode (nonempty-run b (suc n) l) ≡ b :: decode (nonempty-run b n l)
deh-helper b 0 [] = refl
deh-helper b (suc n) [] = refl
deh-helper b 0 (h :: t) = refl
deh-helper b (suc n) (h :: t) = refl

-- 8 points
decode-encodeh : ∀ (b : 𝔹) (r : run) → decode (encodeh b r) ≡ b :: decode r
decode-encodeh b empty-run = refl
decode-encodeh ff (nonempty-run ff rn l) rewrite deh-helper ff rn l = refl
decode-encodeh tt (nonempty-run tt rn l) rewrite deh-helper tt rn l = refl
decode-encodeh ff (nonempty-run tt rn l) = refl
decode-encodeh tt (nonempty-run ff rn l) = refl

mac-decode-encodeh : ∀ (b : bool) (r : run) → decode (encodeh b r) ≡ b :: decode r
mac-decode-encodeh = decode-encodeh

-- 15 points
decode-encode : ∀ (l : 𝕃 𝔹) → decode (encode l) ≡ l
decode-encode [] = refl
decode-encode (h :: t) rewrite decode-encodeh h (encode t) | decode-encode t = refl

mac-decode-encode : ∀ (l : list bool) → decode (encode l) ≡ l
mac-decode-encode = decode-encode

