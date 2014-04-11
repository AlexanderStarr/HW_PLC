module my-bvcalc-main where

import parse
open import lib
open import bvcalc

open import run ptr aut
module parsem = parse ptr aut
open parsem.parse rrs

negate-bvlit : (𝕃 char) → string
negate-bvlit [] = ""
negate-bvlit ('0' :: l) = "1" ^ negate-bvlit l
negate-bvlit ('1' :: l) = "0" ^ negate-bvlit l
negate-bvlit (_ :: l) = "" ^ negate-bvlit l

bitAND : char → char → string
bitAND '1' '1' = "1"
bitAND _ _ = "0"

bitOR : char → char → string
bitOR '0' '0' = "0"
bitOR _ _ = "1"

bitXOR : char → char → string
bitXOR '1' '1' = "0"
bitXOR '0' '0' = "0"
bitXOR _ _ = "1"

eval-BAND : (𝕃 char) → (𝕃 char) → string
eval-BAND [] [] = ""
eval-BAND (b :: t) [] = "0" ^ (eval-BAND t [])
eval-BAND [] (b :: t) = "0" ^ (eval-BAND [] t)
eval-BAND (b1 :: t1) (b2 :: t2) = (bitAND b1 b2) ^ (eval-BAND t1 t2)

eval-BOR : (𝕃 char) → (𝕃 char) → string
eval-BOR [] [] = ""
eval-BOR (b :: t) [] = (bitOR b '0') ^ (eval-BOR t [])
eval-BOR [] (b :: t) = (bitOR '0' b) ^ (eval-BOR [] t)
eval-BOR (b1 :: t1) (b2 :: t2) = (bitOR b1 b2) ^ (eval-BOR t1 t2)

eval-BXOR : (𝕃 char) → (𝕃 char) → string
eval-BXOR [] [] = ""
eval-BXOR (b :: t) [] = (bitXOR b '0') ^ (eval-BXOR t [])
eval-BXOR [] (b :: t) = (bitXOR '0' b) ^ (eval-BXOR [] t)
eval-BXOR (b1 :: t1) (b2 :: t2) = (bitXOR b1 b2) ^ (eval-BXOR t1 t2)

eval-infix : (𝕃 char) → binop → (𝕃 char) → string
eval-infix lc1 (BAND) lc2 = eval-BAND lc1 lc2
eval-infix lc1 (BOR) lc2 = eval-BOR lc1 lc2
eval-infix lc1 (BXOR) lc2 = eval-BXOR lc1 lc2

eval-shift : (𝕃 char) → shiftop → (maybe ℕ) → string
eval-shift _ _ _ = ""

interp-bv : bv → string
interp-bv (Lit b) = b
interp-bv (Paren b) = (interp-bv b)
interp-bv (Negate b) = negate-bvlit (string-to-𝕃char (interp-bv b))
interp-bv (Infix b1 op b2) = eval-infix (string-to-𝕃char (interp-bv b1)) op (string-to-𝕃char (interp-bv b2))
interp-bv (Shift b op n) = eval-shift (string-to-𝕃char (interp-bv b)) op (string-to-ℕ n)

process-start : start → string
process-start (Init s) = (interp-bv s) ^ "\n"

process : Run → string
process (State s0 :: State s2 :: ParseTree (parsed-start p) :: State s3 :: State s1 :: []) = process-start p
process r = "Parsing failure (run with -" ^ "-showParsed).\n"

putStrRunIf : 𝔹 → Run → IO ⊤
putStrRunIf tt r = putStr (Run-to-string r) >> putStr "\n"
putStrRunIf ff r = return triv

processArgs : (showRun : 𝔹) → (showParsed : 𝔹) → 𝕃 string → IO ⊤ 
processArgs showRun showParsed (x :: []) = (readFiniteFile x) >>= processText
  where processText : string → IO ⊤
        processText x with runAut x
        processText x | s with s
        processText x | s | inj₁ _ = putStr (runState-to-string s) >> putStr "\nCannot proceed to parsing.\n"
        processText x | s | inj₂ r with putStrRunIf showRun r | rewriteRun r
        processText x | s | inj₂ r | sr | r' with putStrRunIf showParsed r'
        processText x | s | inj₂ r | sr | r' | sr' = sr >> sr' >> putStr (process r')
                                     
processArgs showRun showParsed ("--showRun" :: xs) = processArgs tt showParsed xs 
processArgs showRun showParsed ("--showParsed" :: xs) = processArgs showRun tt xs 
processArgs showRun showParsed (x :: xs) = putStr ("Unknown option " ^ x ^ "\n")
processArgs showRun showParsed [] = putStr "Please run with the name of a file to process.\n"

main : IO ⊤
main = getArgs >>= processArgs ff ff

