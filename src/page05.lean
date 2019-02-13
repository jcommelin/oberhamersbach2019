import algebra.group
import data.set.basic
import analysis.exponential
import tactic.norm_num

set_option pp.beta true

----------------------------------------------

example (P Q R : Prop) :
  ((P ∨ Q → R) ∧ P) → R :=
begin
  rintro ⟨impl, hP⟩,
  apply impl,
  left,
  exact hP,
end

example (P Q R : Prop) :
  ((P ∨ Q → R) ∧ P) → R :=
begin
  finish,
end

example (X : Type) (A B C : set X) :
A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  ext x,
  split,
  { rintro ⟨x_A, x_B | x_C⟩,
    { left,
      apply and.intro,
      { assumption },
      { assumption } },
    { right,
      apply and.intro,
      { assumption },
      { assumption } } },
  { rintro (⟨x_A, x_B⟩|⟨x_A, x_C⟩),
    { apply and.intro,
      { assumption },
      { left,
        assumption } },
    { apply and.intro,
      { assumption },
      { right,
        assumption } } }
end

example (X : Type)
  (A B C : set X) :
A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
by ext x; split; finish

example (X : Type) (A B C : set X) :
A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
set.inter_distrib_left _ _ _

example (X Y : Type) (f : X → Y) :
(∀ y : Y, ∃ x : X, f(x) = y) ↔ (∃ g : Y → X, f ∘ g = id) :=
begin
  split,
  { intro hyp,
    choose g H using hyp,
    use g,
    funext y,
    apply H, },
  { rintros ⟨g, f_circ_g⟩ y,
    use g y,
    apply congr_fun f_circ_g, }
end

example (G H : Type)
  [group G] [group H]
  (f : G → H)
  (Hyp : ∀ a b : G,
    f (a*b) = f a * f b) :
f 1 = 1 :=
begin
  have key := Hyp 1 1,
  replace key := key.symm,
  simp at key,
  assumption,
end

example (u : ℕ → ℝ)
  (H : ∀ n, u (n+1) = 2*u n)
  (H0 : u 0 > 0) :
∀ n, u n > 0 :=
begin
  intro n,
  induction n with n IH,
  { exact H0, },
  { rw H,
    apply mul_pos,
    norm_num,
    exact IH, }
end