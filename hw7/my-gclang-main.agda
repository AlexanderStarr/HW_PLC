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

--------------------
-- General functions
--------------------

-- Our grammar ensures that a loc is always a number, so we want to eliminate the maybe ℕ.
loc-to-ℕ : loc → ℕ
loc-to-ℕ l with (string-to-ℕ l)
loc-to-ℕ l | nothing = 0  -- This should never happen, because only numbers get created as locs.
loc-to-ℕ l | (just n) = n

-- Super handy function to get an element at a certain index.
get-elem : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → ℕ → (maybe A)
get-elem [] n = nothing
get-elem (elem :: elems) 0 = just elem
get-elem (elem :: elems) (suc n) = get-elem elems n

-- Returns the extra field of a cell at a given field.
get-elems-extra : 𝕃 cell → (maybe ℕ) → (maybe ℕ)
get-elems-extra cells nothing = nothing
get-elems-extra cells (just n) with (get-elem cells n)
... | nothing = nothing
... | (just (e , a , b)) = e

-- Another super handy function which replaces the element at a given index with a supplied element.
change-elem : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → ℕ → A → 𝕃 A
change-elem [] n a = []
change-elem (elem :: elems) 0 a = a :: elems
change-elem (elem :: elems) (suc n) a = elem :: (change-elem elems n a)

-- Converts a global extra to a nat.
ge-to-ℕ : (maybe ℕ) → ℕ
ge-to-ℕ nothing = 0
ge-to-ℕ (just n) = n

-- Proof for the get-half function.
2!=0 : ℕ → (2 =ℕ 0 ≡ ff)
2!=0 n = refl

-- Returns the result of having a nat.
get-half : ℕ → ℕ
get-half n = (n ÷ 2 div (2!=0 2))

----------------------------
-- Code for the ref-counting
----------------------------

increment-refcount : ℕ → 𝕃 cell → 𝕃 cell
increment-refcount n [] = []
increment-refcount 0 (((nothing) , a , b) :: cells) = ((just 1) , a , b) :: cells
increment-refcount 0 (((just ref) , a , b) :: cells) = ((just (suc ref)) , a , b) :: cells
increment-refcount (suc n) (c :: cells) = c :: (increment-refcount n cells)

ir-wrap : loc-or-null → 𝕃 cell → 𝕃 cell
ir-wrap Null cells = cells
ir-wrap (Loc l) cells = increment-refcount (loc-to-ℕ l) cells

decrement-refcount : (maybe ℕ) → ‌𝕃 cell → ℕ → 𝕃 cell
decrement-refcount _ cells 0 = cells
decrement-refcount nothing cells (suc count) = cells
decrement-refcount (just index) cells (suc count) with get-elem cells index
... | nothing = cells
... | (just (nothing , a , b)) = (change-elem cells index (nothing , nothing , nothing))
... | (just ((just 0) , a , b)) = (change-elem cells index (nothing , nothing , nothing))
... | (just ((just 1) , a , b)) = change-elem (decrement-refcount b (decrement-refcount a cells count) count) index (nothing , nothing , nothing)
... | (just ((just (suc n)) , a , b)) = change-elem cells index ((just n) , a , b)

assign-field-refcount : loc → one-field → loc-or-null → 𝕃 cell → 𝕃 cell
assign-field-refcount l (FieldA) lon cells with get-elem cells (loc-to-ℕ l)
... | nothing = cells
... | (just (e , a , b)) = ir-wrap lon (decrement-refcount a cells (length cells))
assign-field-refcount l (FieldB) lon cells with get-elem cells (loc-to-ℕ l)
... | nothing = cells
... | (just (e , a , b)) = ir-wrap lon (decrement-refcount b cells (length cells))

-------------------------------------------
-- Code for running minimal gclang programs
-------------------------------------------

add-root : loc → mem → algorithm → mem
add-root l (ge , ln , lc) (ref-counting) = (ge , ((loc-to-ℕ l) :: ln) , (increment-refcount (loc-to-ℕ l) lc))
add-root l (ge , ln , lc) a = (ge , ((loc-to-ℕ l) :: ln) , lc)

drop-root : loc → 𝕃 ℕ → 𝕃 ℕ
drop-root l [] = []
drop-root l (h :: t) = if (l =string (ℕ-to-string h)) then (drop-root l t) else (h :: (drop-root l t))

assign-field : one-field → loc-or-null → cell → cell
assign-field (FieldA) (Null) (n1 , n2 , n3) = (n1 , nothing , n3)
assign-field (FieldB) (Null) (n1 , n2 , n3) = (n1 , n2 , nothing)
assign-field (FieldA) (Loc l) (n1 , n2 , n3) = (n1 , (string-to-ℕ l) , n3)
assign-field (FieldB) (Loc l) (n1 , n2 , n3) = (n1 , n2 , (string-to-ℕ l))

create-loc : loc-or-null → (maybe ℕ) → loc-or-null
create-loc Null ge = Null
create-loc (Loc l) nothing = (Loc l)
create-loc (Loc l) (just n) = (Loc (ℕ-to-string (n + (loc-to-ℕ l))))

-- This takes a location, the field to modify, the location to set it to, a counter, the
-- list of cells, and the global extra field.
assign-fields : loc → one-field → loc-or-null → ℕ → 𝕃 cell → (maybe ℕ) → 𝕃 cell
assign-fields l of lon index [] ge = []
assign-fields l of lon index (h :: t) ge = if (((loc-to-ℕ l) + (ge-to-ℕ ge)) =ℕ index) then ((assign-field of (create-loc lon ge) h) :: t) else (h :: (assign-fields l of lon (suc index) t ge))

-------------------------------------
-- Code for executing the gc commands
-------------------------------------

-- From here to next header is for mark-and-sweep

mark-cell : (maybe ℕ) → 𝕃 cell → 𝕃 cell
mark-cell nothing lc = lc
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

-- From here to the next header is for copy collection

resolve-ptr : cell → 𝕃 cell → cell
resolve-ptr (e , a , b) cells = (e , (get-elems-extra cells a) , (get-elems-extra cells b))

resolve-ptrs : 𝕃 cell → 𝕃 cell → ℕ → ℕ → 𝕃 cell
resolve-ptrs ref-cells [] count end = []
resolve-ptrs ref-cells (cell :: cells) count end with (count =ℕ end)
... | tt = cells
... | ff = (resolve-ptr cell ref-cells) :: (resolve-ptrs ref-cells cells count end)

translate-roots : 𝕃 ℕ → 𝕃 cell → 𝕃 ℕ
translate-roots [] cells = []
translate-roots (root :: roots) cells with (get-elems-extra cells (just root))
... | nothing = 0 :: (translate-roots roots cells)
... | (just n) = n :: (translate-roots roots cells)

advance-copy-to : ℕ → 𝕃 cell → ℕ → ℕ
advance-copy-to index cells 0 = index
advance-copy-to index cells (suc n) with (get-elem cells index)
... | nothing = index
... | (just (nothing , a , b)) = index
... | (just ((just num) , a , b)) = (advance-copy-to (suc index) cells n)

copy-cell : (maybe ℕ) → ℕ → 𝕃 cell → ℕ → 𝕃 cell
copy-cell nothing copy-to cells counter = cells
copy-cell (just curr) copy-to cells 0 = cells
copy-cell (just curr) copy-to cells (suc counter) with (get-elem cells curr)
... | nothing = cells
... | (just ((just n) , a , b)) = cells
... | (just (nothing , a , b)) with (change-elem (change-elem cells copy-to (nothing , a , b)) curr ((just copy-to) , a , b))
...     | updated-cells-1 with (copy-cell a (suc copy-to) updated-cells-1 counter)
...         | updated-cells-2 = (copy-cell b (advance-copy-to (suc copy-to) updated-cells-2 (length cells)) updated-cells-2 counter)

copy-cells : ℕ → 𝕃 ℕ → 𝕃 cell → ℕ → 𝕃 cell
copy-cells ge [] cells copy-to = cells
copy-cells ge (root :: roots) cells copy-to = copy-cells ge roots (copy-cell (just root) copy-to cells (length cells)) (advance-copy-to copy-to cells (length cells))

clear-cells : ℕ → ℕ → ℕ → 𝕃 cell → 𝕃 cell
clear-cells index start end [] = []
clear-cells index start end (cell :: cells) with (start ≤ index) && (index < end)
... | tt = (nothing , nothing , nothing) :: (clear-cells (suc index) start end cells)
... | ff = cell :: (clear-cells (suc index) start end cells)

new-ge : ℕ → ℕ → ℕ
new-ge old-ge list-len = if (old-ge =ℕ (get-half list-len)) then (0) else (get-half list-len)

-- This monstrosity handles all the steps required for copy collection.
-- Essentially, for every root, you follow the graph starting at that root, 
-- and copy everything to the to-space and assign forwarding pointers.
-- Then it does another sweep to fix all the pointers in the to-space (they still point to the from-space).
-- Then, it goes through and fixes all the roots
-- Finally, it clears all of the data in the from-space.
run-copy-collect : mem → mem
run-copy-collect (ge , [] , cells) = ((just (new-ge (ge-to-ℕ ge) (length cells))) , [] , (repeat (length cells) (nothing , nothing , nothing)))
run-copy-collect (ge , roots , cells) with (copy-cells (ge-to-ℕ ge) roots cells (new-ge (ge-to-ℕ ge) (length cells)))
... | new-cells-1 with (resolve-ptrs new-cells-1 new-cells-1 (new-ge (ge-to-ℕ ge) (length cells)) ((new-ge (ge-to-ℕ ge) (length cells)) + (get-half (length cells))))
...     | new-cells-2 = ((just (new-ge (ge-to-ℕ ge) (length cells))) , (translate-roots roots new-cells-2) , (clear-cells 0 (ge-to-ℕ ge) ((ge-to-ℕ ge) + (get-half (length cells))) new-cells-2))

run-gc : mem → algorithm → mem
run-gc m no-mem-management = m
run-gc m ref-counting = m
run-gc m mark-and-sweep = run-mark-and-sweep m
run-gc m copying = run-copy-collect m

--------------------------
-- Code for executing cmds
--------------------------

-- Filters out assign commands for a field which is outside the virtual heap.  For use with --copying.
-- i.e. prevents changing anything in the other half of the heap from being changed.
assign-fields-copying : loc → one-field → loc-or-null → 𝕃 cell → (maybe ℕ) → 𝕃 cell
assign-fields-copying l of lon lc ge with ((loc-to-ℕ l) < (get-half (length lc)))
... | ff = lc
... | tt = assign-fields l of lon 0 lc ge

exec-cmd : cmd → 𝕃 mem → algorithm → 𝕃 mem
exec-cmd c [] a = []
exec-cmd (AddRoot l) (m :: ms) a = (add-root l m a) :: ms
exec-cmd (Assign l of lon) ((ge , ln , lc) :: ms) ref-counting = (ge , ln , (assign-fields l of lon 0 (assign-field-refcount l of lon lc) ge)) :: ms
exec-cmd (Assign l of lon) ((ge , ln , lc) :: ms) copying = (ge , ln , (assign-fields-copying l of lon  lc ge)) :: ms
exec-cmd (Assign l of lon) ((ge , ln , lc) :: ms) a = (ge , ln , (assign-fields l of lon 0 lc ge)) :: ms
exec-cmd (DropRoot l) ((ge , ln , lc) :: ms) ref-counting = (ge , (drop-root l ln) , (decrement-refcount (string-to-ℕ l) lc (length lc))) :: ms
exec-cmd (DropRoot l) ((ge , ln , lc) :: ms) a = (ge , (drop-root l ln) , lc) :: ms
exec-cmd (Gc) (m :: ms) a = (run-gc m a) :: ms
exec-cmd (Snapshot) (m :: ms) a = m :: m :: ms

exec-cmds : cmds → 𝕃 mem → algorithm → 𝕃 mem
exec-cmds (CmdsLast c) lm a = lm
exec-cmds (CmdsNext c cs) lm a = exec-cmds cs (exec-cmd c lm a) a

init-mem : maybe ℕ → algorithm → mem
init-mem nothing a = (nothing , [] , [])
init-mem (just n) (copying) = ((just 0) , [] , (repeat (n + n) (nothing , nothing , nothing)))
init-mem (just n) a = (nothing , [] , (repeat n (nothing , nothing , nothing)))

process-start : start → algorithm → 𝕃 mem
process-start (Strt (InitHeap n) cmds) a = reverse (exec-cmds cmds ((init-mem (string-to-ℕ n) a) :: []) a)

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

gen-nodes : mem → string
gen-nodes m = "s0 [label = \"s0\"];\ns1 [label = \"s1\"];\n"

gen-edges : mem → string
gen-edges m = "s0 -> s1;\n"

mem-to-graphviz : mem → string
mem-to-graphviz h = "digraph mem {\nrankdir = LR;\nnode [shape = circle];\n" ^ (gen-nodes h) ^ (gen-edges h) ^ "}"

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

