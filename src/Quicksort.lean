import algebra.order
import tactic



private def only_those {T : Type} (cond : T → T → Prop) [∀ n, ∀ m, decidable (cond n m)] : T → list T → list T
| p []        := []
| p (x :: xs) := if (cond x p) then x :: only_those p xs else only_those p xs

private lemma size_cap {T : Type} {cond : T → T → Prop} [∀ n, ∀ m, decidable (cond n m)] {pivot : T} {lizt : list T} :
  (only_those cond pivot lizt).sizeof < (pivot :: lizt).sizeof
  :=
begin
  induction lizt with head tail ih,
    unfold only_those,
    unfold list.sizeof,
    linarith,

    unfold list.sizeof,
    have siz : (pivot :: tail).sizeof = (1 + (sizeof pivot) + tail.sizeof),
      unfold list.sizeof,
    -- by_cases cond head pivot,
    calc (only_those cond pivot (head :: tail)).sizeof 
         ≤ 1 + (sizeof head) + (only_those cond pivot tail).sizeof : by sorry     -- why cannot `unfold only_those` 
    ...  < 1 + (sizeof head) + (pivot :: tail).sizeof              : by linarith  -- uses `ih` and `add_le_add` afaik
    ...  = 1 + (sizeof head) + (1 + (sizeof pivot) + tail.sizeof)  : by linarith, -- uses `siz`
end


variable {L : Type}
variable [linear_order L]

private def only_le : L → list L → list L :=
  only_those (≤)

private def only_gt : L → list L → list L :=
  only_those (>)


def kviksort : list L → list L
| []        := []
| (x :: xs) := have (only_le x xs).sizeof < (x :: xs).sizeof, from size_cap,
               have (only_gt x xs).sizeof < (x :: xs).sizeof, from size_cap,
               kviksort (only_le x xs) ++ [x] ++ kviksort (only_gt x xs)


#eval kviksort [14, 8, 2, 20, 15, 0, 11, 18, 7, 6, 3, 13, 10, 17, 1, 4, 5, 9, 19, 12, 16, 10]
-- Result should be a sequence of integers 0..20 where 10 is twice.