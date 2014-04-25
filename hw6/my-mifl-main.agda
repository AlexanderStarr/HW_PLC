module my-mifl-main where

import parse
open import lib
open import mifl

module parsem = parse ptr state aut
open parsem
open parsem.parse rrs

---------------------------------
-- Code for the printMifl option
---------------------------------

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

-------------------------------
-- Code for the emitJava option
-------------------------------

maybe-paren : type → ℕ → string
maybe-paren (ParType t) n = maybe-paren t n
maybe-paren (Arrow t1 t2) 0 = "("
maybe-paren (Arrow t1 t2) _ = " + \")"
maybe-paren (Type2Symb s) _ = ""

maybe-more-toString : type → string
maybe-more-toString (ParType t) = maybe-more-toString t
maybe-more-toString (Arrow t1 t2) = " \" + "
maybe-more-toString (Type2Symb s) = ""

emit-arg-piece : symb → symb → ℕ → ℕ → string
emit-arg-piece s1 s2 n1 0 = "protected " ^ s2 ^ " " ^ s1 ^ "_data" ^ (ℕ-to-string n1) ^ ";"
emit-arg-piece s1 s2 n1 1 = s2 ^ " " ^ s1 ^ "_data" ^ (ℕ-to-string n1)
emit-arg-piece s1 s2 n1 2 = "this." ^ s1 ^ "_data" ^ (ℕ-to-string n1) ^ " = " ^ s1 ^ "_data" ^ (ℕ-to-string n1) ^ ";"
emit-arg-piece s1 s2 n1 3 = "public " ^ s2 ^ " get_" ^ s1 ^ "_data" ^ (ℕ-to-string n1) ^ "() {return " ^ s1 ^ "_data" ^ (ℕ-to-string n1) ^ ";}"
emit-arg-piece s1 s2 n1 4 = "(" ^ s1 ^ "_data" ^ (ℕ-to-string n1) ^ ".toString())"
emit-arg-piece s1 s2 n1 _ = ""

emit-arg-delim : ℕ → string
emit-arg-delim 0 = ""
emit-arg-delim 1 = ", "
emit-arg-delim 2 = ""
emit-arg-delim 3 = "\n"
emit-arg-delim 4 = " + "
emit-arg-delim _ = ""

emit-constr-arg : symb → type → ℕ → ℕ → string
emit-constr-arg s1 (Type2Symb s2) n1 n2 = emit-arg-piece s1 s2 n1 n2
emit-constr-arg s1 (ParType t) n1 n2 = emit-constr-arg s1 t n1 n2
emit-constr-arg s1 (Arrow t1 t2) n1 n2 = (emit-constr-arg s1 t1 (suc n1) n2) ^ (emit-arg-delim n2) ^ (emit-constr-arg s1 t2 n1 n2)

emit-constr-args : symb → type → ℕ → string
emit-constr-args s1 (Type2Symb s2) n = ""
emit-constr-args s (ParType t) n = emit-constr-args s t n
emit-constr-args s (Arrow t1 t2) n = emit-constr-arg s t1 0 n

emit-constr-def : symb → constr → string
emit-constr-def s1 (Constr s2 t) = "public static class " ^ s2 ^ " extends " ^ s1 ^ "{\npublic int getTag() {\n return " ^ s2 ^ "_TAG;\n}" ^ (emit-constr-args s2 t 0) ^ "\npublic " ^ s2 ^ "(" ^ (emit-constr-args s2 t 1) ^ ") {" ^ (emit-constr-args s2 t 2) ^ "}\n" ^ (emit-constr-args s2 t 3) ^ "\npublic String toString() {\n return \"" ^ (maybe-paren t 0) ^ s2 ^ (maybe-more-toString t) ^ (emit-constr-args s2 t 4) ^ (maybe-paren t 1) ^ "\";\n}}"

emit-constrlist-defs : symb → constrlist → string
emit-constrlist-defs s (EmptyCList) = ""
emit-constrlist-defs s (CList cl c) = (emit-constrlist-defs s cl) ^ (emit-constr-def s c)

emit-constr-defs : symb → dbody → string
emit-constr-defs s (EmptyDBody) = ""
emit-constr-defs s (NonEmptyDBody cl c) = (emit-constrlist-defs s cl) ^ (emit-constr-def s c)

emit-constr : constr → ℕ → string
emit-constr (Constr s t) n = "public static int " ^ s ^ "_TAG = " ^ (ℕ-to-string n) ^ ";\n"

emit-constrlist : constrlist → ℕ → string
emit-constrlist (EmptyCList) n = ""
emit-constrlist (CList cl c) n = (emit-constrlist cl (suc n)) ^ (emit-constr c n)

emit-dbody : dbody → string
emit-dbody (EmptyDBody) = ""
emit-dbody (NonEmptyDBody cl c) = (emit-constrlist cl 1) ^ (emit-constr c 0)

emit-data : symb → dbody → string
emit-data s d = "public static abstract class " ^ s ^ " {\n" ^ (emit-dbody d) ^ "public abstract int getTag();}\n" ^ (emit-constr-defs s d)

emit-return-type : type → string
emit-return-type (Type2Symb s) = s
emit-return-type (ParType t) = emit-return-type t
emit-return-type (Arrow t1 t2) = emit-return-type t2

emit-fun-def : fbody → string
emit-fun-def f = ""

get-input-type : type → type → type
get-input-type t1 (Type2Symb t2) = t1
get-input-type t1 (ParType t2) = get-input-type t1 t2
get-input-type t1 (Arrow t2 t3) = (Arrow t1 (get-input-type t2 t3))

emit-input : type → ℕ → string
emit-input (Type2Symb s) n = s ^ " x" ^ (ℕ-to-string n)
emit-input (ParType t) n = emit-input t n
emit-input (Arrow t1 t2) n = (emit-input t1 n) ^ ", " ^ (emit-input t2 (suc n))

emit-inputs : type → string
emit-inputs (Type2Symb s) = ""
emit-inputs (ParType t) = emit-inputs t
emit-inputs (Arrow t1 t2) = emit-input (get-input-type t1 t2) 0

emit-fun : symb → type → fbody → string
emit-fun s t f = "public static " ^ (emit-return-type t) ^ " " ^ s ^ "(" ^ (emit-inputs t) ^ ") {\n" ^ (emit-fun-def f) ^ "\n}"

emit-command : command → string
emit-command (Data (Declare s db)) = emit-data s db
emit-command (Func (Defn s t fb)) = emit-fun s t fb

emit-commands : commands → string
emit-commands (CommandsStart c) = emit-command c 
emit-commands (CommandsNext c cs) = (emit-command c) ^ "\n" ^ (emit-commands cs)

emit-Java : 𝔹 → start → string
emit-Java ff s = ""
emit-Java tt (Strt c) = "\n public class output {\n" ^ (emit-commands c) ^ "\n}\n"

---------------------------------
-- Code for process-start and other emitted code
---------------------------------

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

