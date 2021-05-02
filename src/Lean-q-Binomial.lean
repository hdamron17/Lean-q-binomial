import data.real.basic


--- rising and falling factorials
def falling_qfact (q: ℝ) (n k: ℕ) : ℝ :=
finset.prod (finset.range k) (λ i, 1 - q^(n-i))

def rising_qfact (q: ℝ) (k: ℕ) : ℝ :=
finset.prod (finset.range k) (λ i, 1 - q^(i+1))


--- q-binomial coefficient
noncomputable def qbinom (q: ℝ) (n k: ℕ) : ℝ := (falling_qfact q n k) / (rising_qfact q k)


--- Some lemmas for splitting up the problem
lemma q_pow_n_ne_one (q: ℝ) (n: ℕ) (qpos: q ≥ 0) (qn1: q ≠ 1) (npos: 0 < n) :
q^n ≠ 1 :=
begin
  cases ne.lt_or_lt qn1,
  have q_pow_lt_one := pow_lt_pow_of_lt_left h qpos npos,
  rw one_pow at q_pow_lt_one,
  exact ne_of_lt q_pow_lt_one,

  have q_pow_lt_one := pow_lt_pow_of_lt_left h zero_le_one npos,
  rw one_pow at q_pow_lt_one,
  exact ne_of_gt q_pow_lt_one,
end

lemma one_minus_q_pow_n_ne_zero (q: ℝ) (n: ℕ) (qpos: q ≥ 0) (qn1: q ≠ 1) (npos: 0 < n) :
1 - q^n ≠ 0 :=
begin
  have q_pow_n_ne_one := q_pow_n_ne_one q n qpos qn1 npos,
  rw ne_comm at q_pow_n_ne_one,
  exact sub_ne_zero_of_ne q_pow_n_ne_one,
end

lemma q_expand_one (q: ℝ) (n k: ℕ) (qpos: q ≥ 0) (qn1: q ≠ 1) (npos: 0 < n) (kln: k ≤ n) :
(1 : ℝ) = q^k * (1 - q^(n-k)) / (1 - q^n) + (1 - q^k) / (1 - q^n) :=
begin
  have denom_nonzero := one_minus_q_pow_n_ne_zero q n qpos qn1 npos,
  symmetry,
  rw div_eq_mul_inv,
  rw div_eq_mul_inv,
  rw ← right_distrib,
  rw sub_eq_neg_add,
  rw left_distrib,
  rw ← neg_mul_eq_mul_neg,
  rw ← pow_add,
  rw nat.add_sub_of_le,
  simp,
  rw ← sub_eq_neg_add,
  rw mul_inv_cancel denom_nonzero,
  exact kln,
end

lemma rising_fact_rec2 (q: ℝ) (n k: ℕ) (qpos: q ≥ 0) (qn1: q ≠ 1) (npos: 0 < n) (kpos: 0 < k) (kln: k ≤ n) :
(1 - q ^ (n - k)) / (1 - q ^ n) * (falling_qfact q n k) = (falling_qfact q (n-1) k) :=
begin
  have denom_nonzero := one_minus_q_pow_n_ne_zero q n qpos qn1 npos,
  rw falling_qfact,
  rw mul_comm,
  rw div_eq_mul_inv,
  rw ← mul_assoc,
  rw ← finset.prod_range_succ,
  rw finset.prod_range_succ',
  rw nat.sub_zero,
  rw mul_assoc,
  rw mul_inv_cancel denom_nonzero,
  simp,
  conv in (λ (i : ℕ), 1 - q ^ (n - (i + 1))) {
    rw add_comm,
    rw ← nat.sub_sub,
  },
  rw ← falling_qfact,
end

lemma falling_fact_rec (q: ℝ) (n k: ℕ) (qpos: q ≥ 0) (qn1: q ≠ 1) (npos: 0 < n) (kpos: 0 < k) (kln: k ≤ n) :
(falling_qfact q n k) = (1 - q ^ n) * (falling_qfact q (n-1) (k-1)) :=
begin
  symmetry,
  rw falling_qfact,
  rw mul_comm,
  conv in (λ (i : ℕ), 1 - q ^ (n - 1 - i)) {
    rw nat.sub_sub,
    rw add_comm,
  },
  conv in (1 - q ^ n) { rw ← nat.sub_zero n },
  rw ← finset.prod_range_succ' (λ (i : ℕ), 1 - q ^ (n - i)),
  rw ← falling_qfact,
  rw nat.sub_add_cancel,
  exact nat.succ_le_of_lt kpos,
end

lemma rising_fact_rec (q: ℝ) (k: ℕ) (qpos: q ≥ 0) (qn1: q ≠ 1) (kpos: 0 < k):
(rising_qfact q k) = (1 - q ^ k) * (rising_qfact q (k-1)) :=
begin
  symmetry,
  rw rising_qfact,
  conv in (1 - q^k) { rw ← nat.sub_add_cancel (nat.succ_le_of_lt kpos), },
  rw mul_comm,
  rw ← finset.prod_range_succ,
  rw nat.sub_add_cancel,
  rw ← rising_qfact,
  exact nat.succ_le_of_lt kpos,
end


--- Recurrence for q-binomial coefficients
theorem qbinom_recurrence (q: ℝ) (n k: ℕ) (qpos: q ≥ 0) (qn1: q ≠ 1) (npos: 0 < n) (kpos: 0 < k) (kln: k ≤ n) :
qbinom q n k = q^k * qbinom q (n-1) k + qbinom q (n-1) (k-1) :=
begin
  -- rw qbinom, rw falling_qfact, rw rising_qfact,  -- Unwrap left side
  rw ← one_mul (qbinom q n k),
  rw q_expand_one q n k qpos qn1 npos kln,
  rw right_distrib,
  rw qbinom,
  rw mul_comm (q^k),
  rw ← div_mul_eq_mul_div,
  rw mul_comm _ (q^k),
  rw mul_assoc,
  rw mul_comm ((1 - q ^ (n - k)) / (1 - q ^ n)),
  rw div_mul_eq_mul_div _ _ (rising_qfact q k),
  rw mul_comm (falling_qfact q n k),
  rw (rising_fact_rec2 q n k qpos qn1 npos kpos kln),
  rw ← qbinom,

  rw add_comm,
  rw (falling_fact_rec q n k qpos qn1 npos kpos kln),
  rw (rising_fact_rec q k qpos qn1 kpos),
  rw ← div_mul_div,
  rw ← qbinom,
  rw ← mul_assoc,
  rw div_mul_div,
  rw mul_comm (1 - q ^ k),
  rw div_self,
  simp,
  rw add_comm,

  -- Make sure we can do div_self
  have q_pos_n_ne_zero := one_minus_q_pow_n_ne_zero q n qpos qn1 npos,
  have q_pos_k_ne_zero := one_minus_q_pow_n_ne_zero q k qpos qn1 kpos,
  exact (mul_ne_zero q_pos_n_ne_zero q_pos_k_ne_zero),
end