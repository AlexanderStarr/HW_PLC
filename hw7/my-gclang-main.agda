module my-gclang-main where

import parse
open import lib
open import gclang

module parsem = parse ptr state aut
open parsem
open parsem.parse rrs

{- a cell is a nested pair of the form (extra, fielda, fieldb),
   where each of the components is either nothing or else
   just N.  This N can be any extra data needed by the 
   memory-management algorithm, in the case of the component
   called "extra".  For fielda and fieldb, N is the address
   of another cell. -}
cell : Set
cell = (maybe ℕ) × (maybe ℕ) × (maybe ℕ)

mem : Set
mem = 𝕃 ℕ × 𝕃 cell

{- an algorithm is just a name for a particular memory-management
  algorithm which should be applied by process-start -}
data algorithm : Set where
  no-mem-management : algorithm
  ref-counting : algorithm
  mark-and-sweep : algorithm
  copying : algorithm

-- Our grammar ensures that a loc is always a number, so we want to eliminate the maybe ℕ.
loc-to-ℕ : loc → ℕ
loc-to-ℕ l with (string-to-ℕ l)
loc-to-ℕ l | nothing = 0  -- This should never happen, because only numbers get created as locs.
loc-to-ℕ l | (just n) = n

add-root : loc → mem → mem
add-root l (ln , lc) = (((loc-to-ℕ l) :: ln) , lc)

drop-root : loc → 𝕃 ℕ → 𝕃 ℕ
drop-root l [] = []
drop-root l (h :: t) = if (l =string (ℕ-to-string h)) then (drop-root l t) else (h :: (drop-root l t))

assign-field : one-field → loc-or-null → cell → cell
assign-field (FieldA) (Null) (n1 , n2 , n3) = (n1 , nothing , n3)
assign-field (FieldB) (Null) (n1 , n2 , n3) = (n1 , n2 , nothing)
assign-field (FieldA) (Loc l) (n1 , n2 , n3) = (n1 , (string-to-ℕ l) , n3)
assign-field (FieldB) (Loc l) (n1 , n2 , n3) = (n1 , n2 , (string-to-ℕ l))

assign-fields : loc → one-field → loc-or-null → ℕ → 𝕃 cell → 𝕃 cell
assign-fields l of lon index [] = []
assign-fields l of lon index (h :: t) = if (l =string (ℕ-to-string index)) then ((assign-field of lon h) :: t) else (h :: (assign-fields l of lon (suc index) t))

exec-cmd : cmd → 𝕃 mem → 𝕃 mem
exec-cmd c [] = []
exec-cmd (AddRoot l) (m :: ms) = (add-root l m) :: ms
exec-cmd (Assign l of lon) ((ln , lc) :: ms) = (ln , (assign-fields l of lon 0 lc)) :: ms
exec-cmd (DropRoot l) ((ln , lc) :: ms) = ((drop-root l ln) , lc) :: ms
exec-cmd (Gc) lm = lm
exec-cmd (Snapshot) (m :: ms) = m :: m :: ms

exec-cmds : cmds → 𝕃 mem → 𝕃 mem
exec-cmds (CmdsLast c) lm = lm
exec-cmds (CmdsNext c cs) lm = exec-cmds cs (exec-cmd c lm)

init-mem : maybe ℕ → mem
init-mem nothing = ([] , [])
init-mem (just n) = ([] , (repeat n (nothing , nothing , nothing)))

process-start : start → algorithm → 𝕃 mem
process-start (Strt (InitHeap n) cmds) a = reverse (exec-cmds cmds ((init-mem (string-to-ℕ n)) :: []))

process : Run → algorithm → 𝕃 mem ⊎ string
process (_ :: _ :: ParseTree (parsed-start p) :: _ :: _ :: []) a = inj₁ (process-start p a)
process r _ = inj₂ ("Parsing failure (run with -" ^ "-showParsed).\n")

field-to-string : maybe ℕ → string
field-to-string nothing = "-"
field-to-string (just x) = ℕ-to-string x

cell-to-string : cell → string
cell-to-string (extra , fa , fb) = field-to-string extra ^ " : " ^ field-to-string fa ^ " . " ^ field-to-string fb ^ "\n"

mem-to-string : mem → string
mem-to-string (roots , cells) = "roots: " ^ 𝕃-to-string ℕ-to-string " " roots ^ "\n" ^ string-concat (map cell-to-string cells)

mem-to-graphviz : mem → string
mem-to-graphviz h = "not implemented yet"

dumpMems-h : ℕ → 𝕃 mem → IO ⊤
dumpMems-h n [] = return triv
dumpMems-h n (h :: hs) = writeFile ("mem"^(ℕ-to-string n)^".txt") (mem-to-string h) >> 
                          writeFile ("mem"^(ℕ-to-string n)^".gv") (mem-to-graphviz h) >> 
                          dumpMems-h (suc n) hs

dumpMems : 𝕃 mem → IO ⊤
dumpMems hs = dumpMems-h 0 hs

putStrRunIf : 𝔹 → Run → IO ⊤
putStrRunIf tt r = putStr (Run-to-string r) >> putStr "\n"
putStrRunIf ff r = return triv

processArgs : (showRun : 𝔹) → (showParsed : 𝔹) → (a : algorithm) → 𝕃 string → IO ⊤ 
processArgs showRun showParsed a (x :: []) = (readFiniteFile x) >>= processText
  where processText : string → IO ⊤
        processText x with runAut x
        processText x | s with s
        processText x | s | inj₁ _ = putStr (runState-to-string s) >> putStr "\nCannot proceed to parsing.\n"
        processText x | s | inj₂ r with putStrRunIf showRun r | rewriteRun r
        processText x | s | inj₂ r | sr | r' with putStrRunIf showParsed r' | process r' a
        processText x | s | inj₂ r | sr | r' | sr' | inj₁ hs = sr >> sr' >> dumpMems hs
        processText x | s | inj₂ r | sr | r' | sr' | inj₂ m = sr >> sr' >> putStr m
                                     
processArgs showRun showParsed a ("--showRun" :: xs) = processArgs tt showParsed a xs 
processArgs showRun showParsed a ("--showParsed" :: xs) = processArgs showRun tt a xs 
processArgs showRun showParsed a ("--ref-counting" :: xs) = processArgs showRun showParsed ref-counting xs 
processArgs showRun showParsed a ("--mark-and-sweep" :: xs) = processArgs showRun showParsed mark-and-sweep xs 
processArgs showRun showParsed a ("--copying" :: xs) = processArgs showRun showParsed copying xs 
processArgs showRun showParsed a (x :: xs) = putStr ("Unknown option " ^ x ^ "\n")
processArgs showRun showParsed a [] = putStr "Please run with the name of a file to process.\n"

main : IO ⊤
main = getArgs >>= processArgs ff ff ref-counting

