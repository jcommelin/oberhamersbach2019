import tactic.interactive tactic.tidy

namespace nat

lemma dvd_add_iff_right_of_left (k m n : ℕ) (h : k ∣ m) :
  k ∣ n ↔ k ∣ m + n :=
nat.dvd_add_iff_right h

lemma dvd_right_of_dvd_add_of_dvd_left (k m n : ℕ) (h : k ∣ m) :
  k ∣ m + n → k ∣ n :=
(dvd_add_iff_right_of_left _ _ _ h).mpr

end nat

namespace tactic
namespace interactive
open interactive interactive.types

meta def use_this (l : parse pexpr_list_or_texpr) : tactic unit :=
(tactic.use l >> (triv <|> try `[apply exists_prop.mpr]))

@[tidy] meta def auto_aux : tactic unit :=
`[solve_by_elim [fact_ne_zero
                ,nat.dvd_right_of_dvd_add_of_dvd_left
                ,prime.not_dvd_one
                ,prime.pos
                ,nat.min_fac_dvd
                ,nat.dvd_fact
                ,le_of_not_ge]]

meta def auto : tactic unit := auto_aux <|> tidy

end interactive
end tactic
