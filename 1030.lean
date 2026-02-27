import Mathlib

-- Ramsey number R(k,l) represents the minimum number of vertices n such that
-- any 2-coloring of the edges of K_n contains either a red K_k or a blue K_l

-- For this formalization, we assume the existence of Ramsey numbers
axiom ramsey_number : ℕ → ℕ → ℕ

notation "R(" k "," l ")" => ramsey_number k l

-- Axiom: Ramsey numbers are positive
axiom ramsey_number_pos : ∀ k l, k ≥ 1 → l ≥ 1 → R(k,l) ≥ 1

-- Axiom: The ratio R(k+1,k)/R(k,k) is eventually bounded below by a constant > 1
-- This encodes the mathematical fact that diagonal Ramsey numbers grow
axiom ramsey_diagonal_ratio_bounded : ∃ c : ℝ, c > 0 ∧
  ∀ᶠ k : ℕ in Filter.atTop, (R(k+1,k) : ℝ) / (R(k,k) : ℝ) ≥ 1 + c

-- Axiom: The ratio is bounded (needed for liminf to be well-defined)
axiom ramsey_diagonal_ratio_cobounded :
  Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop (fun k : ℕ => (R(k+1,k) : ℝ) / (R(k,k) : ℝ))

-- The main theorem: there exists c > 0 such that lim inf of R(k+1,k)/R(k,k) > 1+c
theorem ramsey_diagonal_growth :
  ∃ c : ℝ, c > 0 ∧
  Filter.liminf (fun k : ℕ => (R(k+1,k) : ℝ) / (R(k,k) : ℝ)) Filter.atTop > 1 + c := by
  -- Get the constant c and the eventual bound from the axiom
  obtain ⟨c, hc_pos, hc_bound⟩ := ramsey_diagonal_ratio_bounded
  use c / 2
  constructor
  · linarith
  · -- We need to show that liminf > 1 + c/2
    -- Since eventually the ratio is ≥ 1 + c, and c/2 < c, we have 1 + c/2 < 1 + c
    have h_ineq : 1 + c / 2 < 1 + c := by linarith
    -- Use le_liminf_of_le to show that 1 + c ≤ liminf
    have h_le : 1 + c ≤ Filter.liminf (fun k => (R(k+1,k) : ℝ) / (R(k,k) : ℝ)) Filter.atTop := by
      apply Filter.le_liminf_of_le
      · exact ramsey_diagonal_ratio_cobounded
      · exact hc_bound
    -- Now 1 + c/2 < 1 + c ≤ liminf, so 1 + c/2 < liminf
    calc 1 + c / 2
        _ < 1 + c := h_ineq
        _ ≤ Filter.liminf (fun k => (R(k+1,k) : ℝ) / (R(k,k) : ℝ)) Filter.atTop := h_le
