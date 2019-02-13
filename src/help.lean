
namespace nat

variables {m n : ℕ}

lemma dvd_add_iff_right_of_left (k : ℕ) (h : k ∣ m) :
  k ∣ n ↔ k ∣ m + n :=
nat.dvd_add_iff_right h

end nat
