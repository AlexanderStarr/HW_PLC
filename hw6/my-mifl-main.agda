module my-mifl-main where

import parse
open import lib
open import mifl

module parsem = parse ptr state aut
open parsem
open parsem.parse rrs

print-Mifl : 𝔹 → start → string
print-Mifl ff s = ""
print-Mifl b s = "PRINTING MIFL\n"

check-Types : 𝔹 → start → string
check-Types ff s = ""
check-Types b s = "CHECKING TYPES\n"

emit-Java : 𝔹 → start → string
emit-Java ff s = ""
emit-Java b s = "EMITTING JAVA\n"

process-start : 𝔹 → 𝔹 → 𝔹 → start → string
process-start pM cT eJ s = (print-Mifl pM s) ^ (check-Types cT s) ^ (emit-Java eJ s)

process : 𝔹 → 𝔹 → 𝔹 → Run → string
process printMifl checkTypes emitJava (_ :: _ :: ParseTree (parsed-start p) :: _ :: _ :: []) = process-start printMifl checkTypes emitJava p
process printMifl checkTypes emitJava r = "Parsing failure (run with -" ^ "-showParsed).\n"

putStrRunIf : 𝔹 → Run → IO ⊤
putStrRunIf tt r = putStr (Run-to-string r) >> putStr "\n"
putStrRunIf ff r = return triv

processArgs : (showRun : 𝔹) → (showParsed : 𝔹) → (printMifl : 𝔹) → (checkTypes : 𝔹) → (emitJava : 𝔹) → 𝕃 string → IO ⊤ 
processArgs showRun showParsed printMifl checkTypes emitJava (x :: []) = (readFiniteFile x) >>= processText
  where processText : string → IO ⊤
        processText x with runAut x
        processText x | s with s
        processText x | s | inj₁ _ = putStr (runState-to-string s) >> putStr "\nCannot proceed to parsing.\n"
        processText x | s | inj₂ r with putStrRunIf showRun r | rewriteRun r
        processText x | s | inj₂ r | sr | r' with putStrRunIf showParsed r'
        processText x | s | inj₂ r | sr | r' | sr' = sr >> sr' >> putStr (process printMifl checkTypes emitJava r')
                                     
processArgs showRun showParsed printMifl checkTypes emitJava ("--showRun" :: xs) = processArgs tt showParsed  printMifl checkTypes emitJava xs 
processArgs showRun showParsed printMifl checkTypes emitJava ("--showParsed" :: xs) = processArgs showRun tt printMifl checkTypes emitJava xs 
processArgs showRun showParsed printMifl checkTypes emitJava ("--printMifl" :: xs) = processArgs showRun showParsed tt checkTypes emitJava xs
processArgs showRun showParsed printMifl checkTypes emitJava ("--checkTypes" :: xs) = processArgs showRun showParsed printMifl tt emitJava xs
processArgs showRun showParsed printMifl checkTypes emitJava ("--emitJava" :: xs) = processArgs showRun showParsed printMifl checkTypes tt xs
processArgs showRun showParsed printMifl checkTypes emitJava (x :: xs) = putStr ("Unknown option " ^ x ^ "\n")
processArgs showRun showParsed printMifl checkTypes emitJava [] = putStr "Please run with the name of a file to process.\n"

main : IO ⊤
main = getArgs >>= processArgs ff ff ff ff ff

