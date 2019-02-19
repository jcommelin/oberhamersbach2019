import tactic.interactive tactic.tidy

namespace tactic
namespace interactive
open interactive interactive.types

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
