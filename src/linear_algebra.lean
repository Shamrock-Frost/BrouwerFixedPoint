import linear_algebra.linear_independent
import algebra.big_operators.finsupp

lemma free_module_basis_linear_independent
    (R : Type*) [ring R] (X : Type*)
    : linear_independent R (λ x : X, finsupp.single x (1 : R)) :=
begin
  rw linear_independent_iff,
  intros y h,
  have h' : y.support.sum (λ a, finsupp.single a (y a)) = 0,
  { rw [← h, finsupp.total_apply], dsimp [finsupp.sum],
    congr, ext, simp },
  ext x,
  have h'' : y.support.sum (λ a, finsupp.single a (y a)) x = 0,
  { rw h', simp },
  rw [finset.sum_apply', finset.sum_eq_single x,
      finsupp.single_eq_same] at h'',
  exact h'',
  { intros, rw finsupp.single_apply_eq_zero,
    intro H, symmetry' at H, contradiction },
  { intro H, rw finsupp.not_mem_support_iff at H, rw H, simp }
end

lemma free_module_basis_spanning
    (R : Type*) [ring R] (X : Type*)
    : submodule.span R (set.range (λ x : X, finsupp.single x (1 : R))) = ⊤ :=
begin
  ext f, rw submodule.mem_span, simp,
  intros p hp,
  -- Should extract this as a common lemma
  have : f = (f.support).sum (λ x, finsupp.single x (f x)),
  { ext x, symmetry, rw [finset.sum_apply', finset.sum_eq_single x, finsupp.single_eq_same],
    { intros b hb h, rw finsupp.single_apply_eq_zero, intro, symmetry' at h, contradiction },
    { intro H, rw finsupp.not_mem_support_iff at H, rw H, simp } },
  rw this,
  apply submodule.sum_mem,
  intros x hx,
  rw ← mul_one (f x),
  generalize h : finsupp.single x (f x * 1) = c,
  have := eq.trans (finsupp.smul_single (f x) x 1) h,
  rw ← this,
  apply submodule.smul_mem,
  apply hp,
  existsi x, refl
end