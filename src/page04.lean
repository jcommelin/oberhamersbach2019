import data.nat.prime help

open nat

theorem Euclid (n : ℕ) : ∃ p ≥ n, prime p :=
begin
  let N := n.fact + 1,
  let p := min_fac N,
  use p,
  have hp : prime p :=
  begin
    apply min_fac_prime,
    apply ne_of_gt,
    show 1 < N,
    apply succ_lt_succ,
    apply fact_pos,
  end,
  split,
  { show n ≤ p,
    apply le_of_not_ge,
    assume H,
    apply hp.not_dvd_one,
    have pdvd : p ∣ n.fact :=
    begin
      apply dvd_fact,
      { apply min_fac_pos },
      { assumption }
    end,
    have tada := nat.dvd_add_iff_right pdvd,
    rewrite tada,
    apply min_fac_dvd, },
  { assumption }
end