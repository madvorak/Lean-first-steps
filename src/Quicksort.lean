import algebra.order


private def only_those {T : Type} (cond : T → T → Prop) [∀ n, ∀ m, decidable (cond n m)] : T → list T → list T
| p []        := []
| p (x :: xs) := if (cond x p) then x :: only_those p xs else only_those p xs


variable {L : Type}
variable [linear_order L]

private def only_le : L → list L → list L :=
  only_those (≤)

private def only_gt : L → list L → list L :=
  only_those (>)


def kviksort : list L → list L
| []        := []
| (x :: xs) := kviksort (only_le x xs) ++ [x] ++ kviksort (only_gt x xs)
using_well_founded
{ 
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ l, l.length)⟩],
  dec_tac := `[ sorry ]
}


#eval kviksort [5, 8, 9, 9, 3, 2, 4, 20, 1, 6, 0, 7, 17, 5, 7, 11, 0, 4, 5, 6, 9, 15, 11, 18, 0, 5]