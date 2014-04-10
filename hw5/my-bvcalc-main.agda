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

interp-bv : bv → string
interp-bv (Lit b) = b
interp-bv (Paren b) = (interp-bv b)
interp-bv (Negate b) = negate-bvlit (string-to-𝕃char (interp-bv b))
interp-bv _ = ""

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

