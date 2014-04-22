module my-mifl-main where

import parse
open import lib
open import mifl

module parsem = parse ptr state aut
open parsem
open parsem.parse rrs

print-type : type → string
print-type (Type2Symb s) = s
print-type (ParType t) = "(" ^ (print-type t) ^ ")"
print-type (Arrow t1 t2) = (print-type t1) ^ " -> " ^ (print-type t2)

print-term : term → string
print-term (Term2Symb s) = s
print-term (ParTerm t) = "(" ^ (print-term t) ^ ")"
print-term (App t1 t2) = (print-term t1) ^ " " ^ (print-term t2)

print-constr : constr → string
print-constr (Constr s t) = s ^ " : " ^ (print-type t)

print-constrlist : constrlist → string
print-constrlist (EmptyCList) = ""
print-constrlist (CList cl c) = (print-constrlist cl) ^ (print-constr c) ^ "\n"

print-dbody : dbody → string
print-dbody (EmptyDBody) = ""
print-dbody (NonEmptyDBody cl c) = "\n" ^ (print-constrlist cl) ^ (print-constr c)

print-eqn : eqn → string
print-eqn (Eqn t1 t2) = (print-term t1) ^ " = " ^ (print-term t2) ^ " ."

print-eqnlist : eqnlist → string
print-eqnlist (EmptyEList) = ""
print-eqnlist (EList el e) = (print-eqnlist el) ^ (print-eqn e) ^ "\n"

print-fbody : fbody → string
print-fbody (EmptyFBody) = ""
print-fbody (NonEmptyFBody el e) = "\n" ^ (print-eqnlist el) ^ (print-eqn e)

print-command : command → string
print-command (Data (Declare s db)) = "data " ^ s ^ " where" ^ (print-dbody db)
print-command (Func (Defn s t fb)) = "fun " ^ s ^ " : " ^ (print-type t) ^ (print-fbody fb)

print-commands : commands → string
print-commands (CommandsStart c) = print-command c
print-commands (CommandsNext c cs) = (print-command c) ^ "\n\n" ^ (print-commands cs)

print-Mifl : 𝔹 → start → string
print-Mifl ff s = ""
print-Mifl tt (Strt c) = "\n" ^ (print-commands c) ^ "\n"

check-Types : 𝔹 → start → string
check-Types ff s = ""
check-Types b s = "CHECKING TYPES\n"

emit-Java : 𝔹 → start → string
emit-Java ff s = ""
emit-Java tt (Strt c) = "EMITTING JAVA\n"

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

