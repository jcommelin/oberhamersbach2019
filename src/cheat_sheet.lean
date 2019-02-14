/-                               2019-02-19, Oberhamersbach




Interactive theorem proving with a computer — my experience


--                 _
--                | | ___  __ _ _ __
--                | |/ _ \/ _` | '_ \
--                | |  __| (_| | | | |
--                |_|\___|\__,_|_| |_|
--


A rose-colored introduction




by Johan Commelin -/

















---------------------------------
-- Interactive theorem proving --
---------------------------------
--
--
---- Formal proof verification
--
--
---- Automatic theorem proving































import data.real.basic data.nat.prime help

definition hi := "hello, world!"

#eval hi

#check hi

#check 3

#check ℕ

#check real.sqrt

#check real.sqrt hi

#check (hi : ℝ)

#check 3 = 4

#check (nat.add_comm : ∀ (a b : ℕ), a + b = b + a)

example : ∀ (a b : ℕ), a + b = b + a := nat.add_comm




definition f (x : ℤ) := x^3 + 5 * x - 7

definition FLT : Prop :=
∀ n > 2, ∀ x y z, x^n + y^n = z^n → x = 0 ∨ y = 0

theorem Wiles : FLT :=
begin
  unfold FLT,
  intro n,
  intro hn,
  intros,
  sorry
end




open nat

theorem Euclid (n : ℕ) : ∃ p ≥ n, prime p :=
begin
  let N := n.fact + 1,
  let p := min_fac N,
  use_this p,
  have p_is_prime : prime p,
    apply min_fac_prime,
    have key_fact := n.fact_pos,
    have now : N > 1 := succ_lt_succ key_fact,
    apply ne_of_gt,
    assumption,
  split,
  { by_contradiction contra_hyp,
    have key_fact : p ∣ n.fact,
      apply dvd_fact,
      apply p_is_prime.pos,
      apply le_of_not_ge,
      assumption,
    have oops : p ∣ 1,
      have old_fact : p ∣ n.fact + 1,
        apply min_fac_dvd,
      have tada := p.dvd_add_iff_right_of_left,
      rw tada,
      assumption',
    have old_fact := p_is_prime.not_dvd_one,
    contradiction },
  assumption
end



theorem Euclid' (n : ℕ) : ∃ p ≥ n, prime p :=
begin
  let N := n.fact + 1,
  let p := min_fac N,
  use_this p,
  have p_is_prime : prime p := min_fac_prime _,
  split,
    show p ≥ n,
    by_contradiction,
    have key_fact : p ∣ n.fact := dvd_fact _ _,
    have oops : p ∣ 1,
  all_goals { auto },
end