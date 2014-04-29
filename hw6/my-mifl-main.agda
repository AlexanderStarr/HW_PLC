module my-mifl-main where

import parse
open import lib
open import trie
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

-----------------------------------
-- Code for the printMinMifl option
-----------------------------------

dropParensType : type → type
dropParensType (Arrow t1 (ParType (Arrow t2 t3))) = (dropParensType((Arrow t1 (Arrow t2 t3))))
dropParensType (Arrow t1 t2) = (Arrow (dropParensType t1) (dropParensType t2))
dropParensType (ParType (ParType t)) = (dropParensType (ParType t))
dropParensType (ParType (Type2Symb s)) = (Type2Symb s)
dropParensType (ParType t) = (ParType (dropParensType t))
dropParensType (Type2Symb s) = (Type2Symb s)

dropParensConstr : constr → constr
dropParensConstr (Constr s t) = (Constr s (dropParensType t))

dropParensConstrs : constrlist → constrlist
dropParensConstrs (EmptyCList) = EmptyCList
dropParensConstrs (CList cl c) = (CList (dropParensConstrs cl) (dropParensConstr c))

dropParensTerm : term → term
dropParensTerm (App (ParTerm (App t1 t2)) t3) = (dropParensTerm (App (App t1 t2) t3))
dropParensTerm (App t1 t2) = (App (dropParensTerm t1) (dropParensTerm t2))
dropParensTerm (ParTerm (ParTerm t)) = (dropParensTerm (ParTerm t))
dropParensTerm (ParTerm (Term2Symb s)) = (Term2Symb s)
dropParensTerm (ParTerm t) = (ParTerm (dropParensTerm t))
dropParensTerm (Term2Symb s) = (Term2Symb s)

dropParensEqn : eqn → eqn
dropParensEqn (Eqn t1 t2) = (Eqn (dropParensTerm t1) (dropParensTerm t2))

dropParensEqns : eqnlist → eqnlist
dropParensEqns (EmptyEList) = (EmptyEList)
dropParensEqns (EList el e) = (EList (dropParensEqns el) (dropParensEqn e))

dropParensFBody : fbody → fbody
dropParensFBody (EmptyFBody) = (EmptyFBody)
dropParensFBody (NonEmptyFBody el e) = (NonEmptyFBody (dropParensEqns el) (dropParensEqn e)) 

dropParensCom : command → command
dropParensCom (Data (Declare s (NonEmptyDBody cl c))) = (Data (Declare s (NonEmptyDBody (dropParensConstrs cl) (dropParensConstr c))))
dropParensCom (Func (Defn s t fb)) = (Func (Defn s (dropParensType t) (dropParensFBody fb)))
dropParensCom c = c

dropParensComs : commands → commands
dropParensComs (CommandsStart c) = (CommandsStart (dropParensCom c))
dropParensComs (CommandsNext c cs) = (CommandsNext (dropParensCom c) (dropParensComs cs))

dropParens : start → start
dropParens (Strt c) = (Strt (dropParensComs c))

print-Min-Mifl : 𝔹 → start → string
print-Min-Mifl ff s = ""
print-Min-Mifl tt s = (print-Mifl tt (dropParens s))

---------------------------------
-- Code for the checkTypes option
---------------------------------

data typeInfo : Set where
  isData : typeInfo
  isConstr : symb → typeInfo
  hasType : type → typeInfo

symb-in-trie : symb → (trie typeInfo) → 𝔹
symb-in-trie s tr with trie-lookup tr s
symb-in-trie s tr | nothing = ff
symb-in-trie s tr | just tI = tt

is-dat : symb → (trie typeInfo) → 𝔹
is-dat s tr with trie-lookup tr s
is-dat s tr | just (isData) = tt
is-dat s tr | _ = ff

update-trie-c : symb → constr → (trie typeInfo) → (trie typeInfo)
update-trie-c s1 (Constr s2 t) tr = (trie-insert tr s2 (isConstr s1))

update-trie-cs : symb → constrlist → (trie typeInfo) → (trie typeInfo)
update-trie-cs s (EmptyCList) tr = tr
update-trie-cs s (CList cs c) tr = (update-trie-cs s cs (update-trie-c s c tr))

update-trie-db : symb → dbody → (trie typeInfo) → (trie typeInfo)
update-trie-db s (EmptyDBody) tr = tr
update-trie-db s (NonEmptyDBody cs c) tr = (update-trie-cs s cs (update-trie-c s c tr))

update-trie : command → (trie typeInfo) → (trie typeInfo)
update-trie (Data (Declare s db)) tr = update-trie-db s db (trie-insert tr s (isData))
update-trie (Func (Defn s t fb)) tr = tr

check-type-type : type → (trie typeInfo) → 𝔹
check-type-type (Type2Symb s) tr = is-dat s tr
check-type-type (ParType t) tr = check-type-type t tr
check-type-type (Arrow t1 t2) tr = (check-type-type t1 tr) && (check-type-type t2 tr)

check-constr-type : string → type → (trie typeInfo) → 𝔹
check-constr-type s1 (Type2Symb s2) tr = (s1 =string s2)
check-constr-type s1 (ParType t) tr = check-constr-type s1 t tr
check-constr-type s1 (Arrow t1 t2) tr = (check-type-type t1 tr) && (check-constr-type s1 t2 tr)

check-constr : string → constr → (trie typeInfo) → 𝔹
check-constr s1 (Constr s2 t) tr = (~ (symb-in-trie s2 tr)) && (check-constr-type s1 t tr)

check-constrs : string → constrlist → (trie typeInfo) → 𝔹
check-constrs s1 (EmptyCList) tr = tt
check-constrs s1 (CList cs (Constr s2 t)) tr = (check-constr s1 (Constr s2 t) tr) && (check-constrs s1 cs (trie-insert tr s2 (isConstr s1)))

check-db : string → dbody → (trie typeInfo) → 𝔹
check-db s1 (EmptyDBody) tr = tt
check-db s1 (NonEmptyDBody cs (Constr s2 t)) tr = (check-constr s1 (Constr s2 t) tr) && (check-constrs s1 cs (trie-insert tr s2 (isConstr s1)))

check-eqn-l : term → (trie typeInfo) → 𝔹
check-eqn-l t tr = tt

check-eqn-r : term → (trie typeInfo) → 𝔹
check-eqn-r t tr = tt

update-trie-eqn-l : term → (trie typeInfo) → (trie typeInfo)
update-trie-eqn-l t tr = tr

check-eqn : string → eqn → (trie typeInfo) → 𝔹
check-eqn s (Eqn t1 t2) tr = (check-eqn-l t1 tr) && (check-eqn-r t2 (update-trie-eqn-l t1 tr))

check-elist : string → eqnlist → (trie typeInfo) → 𝔹
check-elist s (EmptyEList) tr = tt
check-elist s (EList el e) tr = (check-eqn s e tr) && (check-elist s el tr)

check-fb : string → fbody → (trie typeInfo) → 𝔹
check-fb s (EmptyFBody) tr = tt
check-fb s (NonEmptyFBody es e) tr = (check-eqn s e tr) && (check-elist s es tr)

check-command : command → (trie typeInfo) → 𝔹
check-command (Data (Declare s db)) tr = (~ (symb-in-trie s tr)) && (check-db s db (trie-insert tr s (isData)))
check-command (Func (Defn s t fb)) tr = (~ (symb-in-trie s tr)) && (check-type-type t tr) && (check-fb s fb (trie-insert tr s (hasType t)))

check-commands : commands → (trie typeInfo) → 𝔹
check-commands (CommandsStart c) tr = check-command c tr
check-commands (CommandsNext c cs) tr = (check-command c tr) && (check-commands cs (update-trie c tr))

is-type-correct : start → 𝔹
is-type-correct (Strt c) = check-commands c (empty-trie)

check-Types : 𝔹 → start → string
check-Types ff s = ""
check-Types b s = if (is-type-correct s) then "" else "type error\n"

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

maybe-elim : (maybe string) → string
maybe-elim nothing = ""
maybe-elim (just string) = string

has-constr : term → (trie string) → 𝔹
has-constr (App t1 t2) tr = (has-constr t1 tr) || (has-constr t2 tr)
has-constr (ParTerm t) tr = has-constr t tr
has-constr (Term2Symb s) tr with trie-lookup tr s
has-constr (Term2Symb s) tr | nothing = ff
has-constr (Term2Symb s) tr | just x = tt

emit-assigns : term → (trie string) → string
emit-assigns t tr = "assignment\n"

term-to-symb : term → symb
term-to-symb (Term2Symb s) =  s
term-to-symb (ParTerm t) = term-to-symb t
term-to-symb (App t1 t2) = term-to-symb t2

emit-return-constrs : term → (trie string) → string
emit-return-constrs (App t1 t2) tr = (emit-return-constrs t1 tr) ^ "(" ^ (emit-return-constrs t2 tr) ^ (if (has-constr t2 tr) then "()" else "") ^ ")"
emit-return-constrs (ParTerm t) tr = emit-return-constrs t tr
emit-return-constrs t tr = (if (has-constr t tr) then ("new " ^ (term-to-symb t)) else (term-to-symb t))

emit-return : term → term → (trie string) → string
emit-return t1 t2 tr = "return " ^ (emit-return-constrs t2 tr) ^ ";\n"

create-con : term → (trie string) → string
create-con t tr = " == "

emit-con : term → term → (trie string) → string
emit-con t1 t2 tr = "if (" ^ (create-con t1 tr) ^ ") {\n" ^ (emit-assigns t1 tr) ^ (emit-return t1 t2 tr)

emit-eqn : eqn → (trie string) → string
emit-eqn (Eqn t1 t2) tr = if (has-constr t1 tr) then ((emit-con t1 t2 tr)) else (emit-return t1 t2 tr)

emit-eqnlist : eqnlist → (trie string) → string
emit-eqnlist (EmptyEList) tr = ""
emit-eqnlist (EList el e) tr = (emit-eqnlist el tr) ^ (emit-eqn e tr)

emit-fbody : fbody → (trie string) → string
emit-fbody (EmptyFBody) tr = ""
emit-fbody (NonEmptyFBody el e) tr = (emit-eqnlist el tr) ^ (emit-eqn e tr)

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

emit-fun : symb → type → fbody → (trie string) → string
emit-fun "main" t (NonEmptyFBody el (Eqn t1 t2)) tr = "public static void main(String[] args) {\n" ^ (emit-return-type t) ^ " main = " ^ (emit-return-constrs t2 tr) ^ ";\n System.out.println(main.toString());\n}"
emit-fun s t f tr = "public static " ^ (emit-return-type t) ^ " " ^ s ^ "(" ^ (emit-inputs t) ^ ") {\n" ^ (emit-fbody f tr) ^ "\n}"

emit-command : command → (trie string) → string
emit-command (Data (Declare s db)) tr = emit-data s db
emit-command (Func (Defn s t fb)) tr = emit-fun s t fb tr

emit-commands : commands → (trie string) → string
emit-commands (CommandsStart c) t = emit-command c t
emit-commands (CommandsNext c cs) t = (emit-command c t) ^ "\n" ^ (emit-commands cs t)

add-constr-to-trie : symb → constr → (trie string) → (trie string)
add-constr-to-trie s1 (Constr s2 t) tr = trie-insert tr s2 s1

add-constrs-to-trie : symb → constrlist → (trie string) → (trie string)
add-constrs-to-trie s (EmptyCList) tr = tr
add-constrs-to-trie s (CList cs c) tr = add-constrs-to-trie s cs (add-constr-to-trie s c tr)

get-data-trie : commands → (trie string) → (trie string)
get-data-trie (CommandsStart (Data (Declare s (NonEmptyDBody cs c)))) tr = add-constrs-to-trie s cs (add-constr-to-trie s c tr)
get-data-trie (CommandsNext (Data (Declare s (NonEmptyDBody cs c))) coms) tr = get-data-trie coms (add-constrs-to-trie s cs (add-constr-to-trie s c tr))
get-data-trie _ tr = tr

emit-Java : 𝔹 → start → string
emit-Java ff s = ""
emit-Java tt (Strt c) = "\n public class output {\n" ^ (emit-commands c (get-data-trie c (empty-trie))) ^ "\n}\n"

---------------------------------
-- Code for process-start and other emitted code
---------------------------------

process-start : 𝔹 → 𝔹 → 𝔹 → 𝔹 → start → string
process-start pM cT eJ pMM s = (print-Mifl pM s) ^ (print-Min-Mifl pMM s) ^ (check-Types cT s) ^ (emit-Java eJ s)

process : 𝔹 → 𝔹 → 𝔹 → 𝔹 → Run → string
process printMifl checkTypes emitJava printMinMifl (_ :: _ :: ParseTree (parsed-start p) :: _ :: _ :: []) = process-start printMifl checkTypes emitJava printMinMifl p
process printMifl checkTypes emitJava printMinMifl r = "Parsing failure (run with -" ^ "-showParsed).\n"

putStrRunIf : 𝔹 → Run → IO ⊤
putStrRunIf tt r = putStr (Run-to-string r) >> putStr "\n"
putStrRunIf ff r = return triv

processArgs : (showRun : 𝔹) → (showParsed : 𝔹) → (printMifl : 𝔹) → (checkTypes : 𝔹) → (emitJava : 𝔹) → (printMinMifl : 𝔹) → 𝕃 string → IO ⊤ 
processArgs showRun showParsed printMifl checkTypes emitJava printMinMifl (x :: []) = (readFiniteFile x) >>= processText
  where processText : string → IO ⊤
        processText x with runAut x
        processText x | s with s
        processText x | s | inj₁ _ = putStr (runState-to-string s) >> putStr "\nCannot proceed to parsing.\n"
        processText x | s | inj₂ r with putStrRunIf showRun r | rewriteRun r
        processText x | s | inj₂ r | sr | r' with putStrRunIf showParsed r'
        processText x | s | inj₂ r | sr | r' | sr' = sr >> sr' >> putStr (process printMifl checkTypes emitJava printMinMifl r')
                                     
processArgs showRun showParsed printMifl checkTypes emitJava printMinMifl ("--showRun" :: xs) = processArgs tt showParsed  printMifl checkTypes emitJava printMinMifl xs 
processArgs showRun showParsed printMifl checkTypes emitJava printMinMifl ("--showParsed" :: xs) = processArgs showRun tt printMifl checkTypes emitJava printMinMifl xs 
processArgs showRun showParsed printMifl checkTypes emitJava printMinMifl ("--printMifl" :: xs) = processArgs showRun showParsed tt checkTypes emitJava printMinMifl xs
processArgs showRun showParsed printMifl checkTypes emitJava printMinMifl ("--checkTypes" :: xs) = processArgs showRun showParsed printMifl tt emitJava printMinMifl xs
processArgs showRun showParsed printMifl checkTypes emitJava printMinMifl ("--emitJava" :: xs) = processArgs showRun showParsed printMifl checkTypes tt printMinMifl xs
processArgs showRun showParsed printMifl checkTypes emitJava printMinMifl ("--printMinMifl" :: xs) = processArgs showRun showParsed printMifl checkTypes emitJava tt xs
processArgs showRun showParsed printMifl checkTypes emitJava printMinMifl (x :: xs) = putStr ("Unknown option " ^ x ^ "\n")
processArgs showRun showParsed printMifl checkTypes emitJava printMinMifl [] = putStr "Please run with the name of a file to process.\n"

main : IO ⊤
main = getArgs >>= processArgs ff ff ff ff ff ff

