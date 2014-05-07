module my-gclang-main where

import parse
open import lib
open import list-merge-sort ℕ _<_
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
mem = maybe ℕ × 𝕃 ℕ × 𝕃 cell

{- an algorithm is just a name for a particular memory-management
  algorithm which should be applied by process-start -}
data algorithm : Set where
  no-mem-management : algorithm
  ref-counting : algorithm
  mark-and-sweep : algorithm
  copying : algorithm

test-mem : mem
test-mem = ( nothing , 3 :: 1 :: 2 :: [] , repeat 3 ( nothing , nothing , nothing ) )

-------------------------------------------
-- Code for running minimal gclang programs
-------------------------------------------

-- Our grammar ensures that a loc is always a number, so we want to eliminate the maybe ℕ.
loc-to-ℕ : loc → ℕ
loc-to-ℕ l with (string-to-ℕ l)
loc-to-ℕ l | nothing = 0  -- This should never happen, because only numbers get created as locs.
loc-to-ℕ l | (just n) = n

add-root : loc → mem → mem
add-root l (ge , ln , lc) = (ge , ((loc-to-ℕ l) :: ln) , lc)

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

-------------------------------------
-- Code for executing the gc commands
-------------------------------------

get-elem : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → ℕ → (maybe A)
get-elem [] n = nothing
get-elem (elem :: elems) 0 = just elem
get-elem (elem :: elems) (suc n) = get-elem elems n

mark-cell : (maybe ℕ) → 𝕃 cell → 𝕃 cell
mark-cell nothing lc = []
mark-cell (just n) [] = []
mark-cell (just 0) ((e , a , b) :: cells) = ((just 1) , a , b) :: cells
mark-cell (just (suc n)) (cell :: cells) = cell :: (mark-cell (just n) cells)

traverse-cells : (maybe ℕ) → 𝕃 cell → ℕ → 𝕃 cell
traverse-cells nothing lc n = lc
traverse-cells (just root) lc 0 = lc
traverse-cells (just root) lc (suc max) with get-elem lc root
... | nothing = lc
... | just (e , a , b) = traverse-cells b (traverse-cells a (mark-cell (just root) lc) max) max

mark-cells : 𝕃 ℕ → 𝕃 cell → ℕ → 𝕃 cell
mark-cells [] cells max = cells
mark-cells (root :: roots) cells max = mark-cells roots (traverse-cells (just root) cells max) max

sweep-cells : 𝕃 cell → 𝕃 cell
sweep-cells [] = []
sweep-cells ((nothing , a , b) :: cells) = (nothing , nothing , nothing) :: (sweep-cells cells)
sweep-cells ((just e , a , b) :: cells) = (nothing , a , b) :: (sweep-cells cells)

run-mark-and-sweep : mem → mem
run-mark-and-sweep (ge , roots , cells) = (ge , roots , (sweep-cells (mark-cells roots cells (length cells))))

run-gc : mem → algorithm → mem
run-gc m no-mem-management = m
run-gc m ref-counting = m
run-gc m mark-and-sweep = run-mark-and-sweep m
run-gc m copying = m

exec-cmd : cmd → 𝕃 mem → algorithm → 𝕃 mem
exec-cmd c [] a = []
exec-cmd (AddRoot l) (m :: ms) a = (add-root l m) :: ms
exec-cmd (Assign l of lon) ((ge , ln , lc) :: ms) a = (ge , ln , (assign-fields l of lon 0 lc)) :: ms
exec-cmd (DropRoot l) ((ge , ln , lc) :: ms) a = (ge , (drop-root l ln) , lc) :: ms
exec-cmd (Gc) (m :: ms) a = (run-gc m a) :: ms
exec-cmd (Snapshot) (m :: ms) a = m :: m :: ms

exec-cmds : cmds → 𝕃 mem → algorithm → 𝕃 mem
exec-cmds (CmdsLast c) lm a = lm
exec-cmds (CmdsNext c cs) lm a = exec-cmds cs (exec-cmd c lm a) a

init-mem : maybe ℕ → mem
init-mem nothing = (nothing , [] , [])
init-mem (just n) = (nothing , [] , (repeat n (nothing , nothing , nothing)))

process-start : start → algorithm → 𝕃 mem
process-start (Strt (InitHeap n) cmds) a = reverse (exec-cmds cmds ((init-mem (string-to-ℕ n)) :: []) a)

process : Run → algorithm → 𝕃 mem ⊎ string
process (_ :: _ :: ParseTree (parsed-start p) :: _ :: _ :: []) a = inj₁ (process-start p a)
process r _ = inj₂ ("Parsing failure (run with -" ^ "-showParsed).\n")

field-to-string : maybe ℕ → string
field-to-string nothing = "-"
field-to-string (just x) = ℕ-to-string x

cell-to-string : cell → string
cell-to-string (extra , fa , fb) = field-to-string extra ^ " : " ^ field-to-string fa ^ " . " ^ field-to-string fb ^ "\n"

mem-to-string : mem → string
mem-to-string (global-extra , roots , cells) = "global extra: " ^ (field-to-string global-extra) 
        ^ "\nroots: " ^ 𝕃-to-string ℕ-to-string " " (merge-sort roots) ^ "\n" ^ string-concat (map cell-to-string cells)

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
main = getArgs >>= processArgs ff ff no-mem-management

