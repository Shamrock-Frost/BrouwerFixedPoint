import data.finsupp.basic

lemma finsupp_single_sub_eq_zero_iff {α G} [has_zero G] [decidable_eq α]
  (a a' : α) (b b' : G)
  : finsupp.single a b = finsupp.single a' b' ↔ b = b' ∧ (a = a' ∨ b = 0) :=
begin
  rw @fun_like.ext_iff _ _ _ _ (finsupp.single a b) (finsupp.single a' b'),
  split,
  { intros h,
    have ha := h a, have ha' := h a', 
    rw [finsupp.single_apply, finsupp.single_apply] at ha ha',
    split_ifs at ha ha'; try { contradiction };
    all_goals { split, try { cc } };
    try { left, cc },
    right, cc },
  { intros h x, cases h, subst h_left,
    cases h_right; subst h_right,
    rw [finsupp.single_zero, finsupp.single_zero] }
end