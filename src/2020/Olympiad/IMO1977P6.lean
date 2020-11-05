import data.nat.basic
import tactic

/- This is a formalization of IMO 1977 Problem 6
The solution is by yayups on https://artofproblemsolving.com/community/c6h75980
Problem statement:
Let f: ℕ → ℕ be a function from naturals to naturals which satisfies the inequalit f(f(n))< f(n+1) ∀ n ∈ ℕ.
Prove that for any n we have f(n)=n
-/

lemma imop6 (f: ℕ → ℕ) (h0: ∀ n: ℕ, f(f(n))< f(n+1)): ∀ n: ℕ, f(n)=n:=
begin
    have claim: ∀ x: ℕ, ∀ n: ℕ, x = f n → n ≤ x ,
    {intro x,
    apply nat.strong_induction_on x,
    intros p q n h1,
    cases nat.eq_zero_or_pos n,
        {rw h, simp},
        {replace h_1:= ne_of_gt h,
        have h2:= nat.exists_eq_succ_of_ne_zero h_1, 
        cases h2 with k h2,
        rw nat.succ_eq_add_one at h2, 
        rw h2 at *, rw h1 at *,
        have h3:= h0 k,
        have h4:= q (f (f k)) h3 (f k) (show f( f k) = f( f k), by refl),
        have h5:= q (f k) (gt_of_gt_of_ge h3 h4) k (show f k = f k, by refl),
        have h6:= gt_of_gt_of_ge h3 h4, 
        rw nat.succ_le_iff,
        exact gt_of_gt_of_ge h6 h5}},
    have claim': ∀ (n: ℕ ), n ≤ f n,
        {intro n, apply claim, refl},

    have claim2 : ∀ (n: ℕ ), f n < f(n+1),
        {intro n, exact gt_of_gt_of_ge (h0 n) (claim' (f n))},
    have claim2': ∀ (a b: ℕ ), a≤ b → f a ≤ f b,
        {intros a b g1, rw le_iff_exists_add at g1, cases g1 with c g1, rw g1, clear g1 b,
        induction c with d hd, simp, 
        apply le_trans hd, apply le_of_lt, rw nat.succ_eq_add_one, rw ← add_assoc, exact claim2 (a+d)},
    intro n,
    have h1: f n < n+1,
        {by_contra, push_neg at h, 
        replace claim2':= claim2' (n+1) (f n) h,
        replace h0:= h0 n, linarith},
    replace claim':= claim' n, linarith
end

 
