import tactic.interactive

namespace nat

variables {m n : ℕ}

lemma dvd_add_iff_right_of_left (k : ℕ) (h : k ∣ m) :
  k ∣ n ↔ k ∣ m + n :=
nat.dvd_add_iff_right h

end nat

namespace tactic
namespace interactive
open interactive interactive.types

meta def use_this (l : parse pexpr_list_or_texpr) : tactic unit :=
(tactic.use l >> (triv <|> try `[rw exists_prop]))

end interactive
end tactic
