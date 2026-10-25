module

public import Mathlib

/-!
# The linearized period map of the circular cell: the normal eigenvalues

Formalization of Lemma `pc:normal-eigenvalues` (and the algebraic facts used in
Lemma `pc:circular-period` and Proposition `pc:period-splitting`) of the paper.

The circular two-interface cell has radii `d₁ = a = √(3/5)` and `d₂ = 1`.  For a positive
frequency `m ∈ 4ℤ` the normal variation obeys `η̇ = i Bₘ η` with
`Bₘ = [[5/4 - m/2, -(3/4) a^{m-2}], [(5/4) a^{m+2}, -3/4]]`, and the period is `P = 4π`.
-/

@[expose] public section

open Real Complex

namespace Euler2D

/-- The inner radius `a = √(3/5)` of the circular two-interface cell. -/
noncomputable def cellA : ℝ := Real.sqrt (3 / 5)

/-- The period `P = 4π` of the circular trajectory. -/
noncomputable def period : ℝ := 4 * π

/-- The Fourier matrix `Bₘ` of the normal variation (Lemma `pc:normal-matrix`). -/
noncomputable def Bmat (m : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![5 / 4 - (m : ℝ) / 2, -(3 / 4) * cellA ^ (m - 2);
     (5 / 4) * cellA ^ (m + 2), -(3 / 4)]

/-- The growth rate `σ = (√15/4) a⁴`. -/
noncomputable def sigma : ℝ := Real.sqrt 15 / 4 * cellA ^ 4

/-- The growing eigenvalue `λ_* = σ - 3i/4` of `i B₄`. -/
noncomputable def lamStar : ℂ := (sigma : ℂ) - 3 / 4 * I

/-- The growing eigenvector `v₊ = (1, i a)`. -/
noncomputable def vPlus : Fin 2 → ℂ := ![1, I * cellA]

/-- The period multiplier `λ = e^{σP}`. -/
noncomputable def lamMult : ℝ := Real.exp (sigma * period)

/-- `Δₘ = (d - √(d² - (15/4) a^{2m}))/2` with `d = m/2 - 2`. -/
noncomputable def DeltaM (m : ℕ) : ℝ :=
  ((m / 2 - 2 : ℝ) - Real.sqrt ((m / 2 - 2 : ℝ) ^ 2 - 15 / 4 * cellA ^ (2 * m))) / 2

lemma cellA_sq : cellA ^ 2 = 3 / 5 := by
  unfold cellA; rw [sq_sqrt]; norm_num

lemma cellA_pos : 0 < cellA := by unfold cellA; positivity

lemma cellA_lt_one : cellA < 1 := by
  unfold cellA; rw [sqrt_lt' one_pos]; norm_num

/-- `√15 · a = 3`. -/
lemma sqrt15_mul_cellA : Real.sqrt 15 * cellA = 3 := by
  unfold cellA
  rw [← Real.sqrt_mul (by norm_num)]
  rw [show (15 : ℝ) * (3 / 5) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `σ = 3a³/4`. -/
lemma sigma_eq : sigma = 3 / 4 * cellA ^ 3 := by
  unfold sigma
  have := sqrt15_mul_cellA
  linear_combination (cellA ^ 3 / 4) * this

/-- The value `σ = 9√15/100` used in the definition of the canonical response data. -/
lemma sigma_eq' : sigma = 9 * Real.sqrt 15 / 100 := by
  unfold sigma
  rw [show cellA ^ 4 = (cellA ^ 2) ^ 2 by ring, cellA_sq]; ring

/-- `e^{(2k+1)πi} = -1`. -/
lemma exp_odd_pi_I (k : ℤ) : Complex.exp ((2 * k + 1) * π * I) = -1 := by
  rw [show (2 * (k : ℂ) + 1) * π * I = k * (2 * π * I) + π * I by ring, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]; ring

lemma sigma_pos : 0 < sigma := by unfold sigma; have := cellA_pos; positivity

/-- At `m = 4`: `i B₄ v₊ = λ_* v₊`. -/
theorem iB4_vPlus :
    (I • (Bmat 4).map (fun r : ℝ => (r : ℂ))).mulVec vPlus = lamStar • vPlus := by
  have h2 := cellA_sq
  have hs := sigma_eq
  ext i; fin_cases i <;>
    simp [Bmat, vPlus, lamStar, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    apply Complex.ext <;> simp [hs, ← Complex.ofReal_pow]
  all_goals (ring_nf; try simp only [show cellA ^ 6 = (cellA ^ 2) ^ 3 by ring,
    show cellA ^ 4 = (cellA ^ 2) ^ 2 by ring, h2]; try ring_nf)

/-- At `m = 4` the other eigenvalue of `i B₄` is `-σ - 3i/4`, with eigenvector `(1, -i a)`. -/
theorem iB4_vMinus :
    (I • (Bmat 4).map (fun r : ℝ => (r : ℂ))).mulVec ![1, -I * cellA] =
      (-(sigma : ℂ) - 3 / 4 * I) • ![1, -I * cellA] := by
  have h2 := cellA_sq
  have hs := sigma_eq
  ext i; fin_cases i <;>
    simp [Bmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    apply Complex.ext <;> simp [hs, ← Complex.ofReal_pow]
  all_goals (ring_nf; try simp only [show cellA ^ 6 = (cellA ^ 2) ^ 3 by ring,
    show cellA ^ 4 = (cellA ^ 2) ^ 2 by ring, h2]; try ring_nf)

/-- `λ = e^{σP} > 1`. -/
lemma one_lt_lamMult : 1 < lamMult := by
  unfold lamMult period
  exact Real.one_lt_exp_iff.mpr (by have := sigma_pos; positivity)

/-- The two period multipliers at `m = 4` are `-λ` and `-λ⁻¹`. -/
theorem period_multipliers_m4 :
    Complex.exp (period * lamStar) = -(lamMult : ℂ) ∧
      Complex.exp (period * (-(sigma : ℂ) - 3 / 4 * I)) = -((lamMult : ℂ))⁻¹ := by
  have key : Complex.exp (-(3 * π) * I) = -1 := by
    convert exp_odd_pi_I (-2) using 2; push_cast; ring
  unfold lamMult lamStar period
  constructor
  · rw [show (4 * π : ℝ) * ((sigma : ℂ) - 3 / 4 * I) = ((sigma * (4 * π) : ℝ) : ℂ)
        + (-(3 * π) * I) by push_cast; ring, Complex.exp_add, key, ← Complex.ofReal_exp]
    ring
  · rw [show (4 * π : ℝ) * (-(sigma : ℂ) - 3 / 4 * I) = ((-(sigma * (4 * π)) : ℝ) : ℂ)
        + (-(3 * π) * I) by push_cast; ring, Complex.exp_add, key, ← Complex.ofReal_exp,
        Real.exp_neg]
    push_cast; ring

section higher

variable {m : ℕ}

lemma cellA_pow_le (hm : 8 ≤ m) : cellA ^ (2 * m) ≤ cellA ^ 16 :=
  pow_le_pow_of_le_one cellA_pos.le cellA_lt_one.le (by omega)

lemma cellA16 : cellA ^ 16 = (3 / 5) ^ 8 := by
  rw [show cellA ^ 16 = (cellA ^ 2) ^ 8 by ring, cellA_sq]

lemma disc_pos (hm : 8 ≤ m) :
    0 < ((m / 2 - 2 : ℝ)) ^ 2 - 15 / 4 * cellA ^ (2 * m) := by
  have h1 := cellA_pow_le hm
  have h2 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have h3 : (2 : ℝ) ≤ m / 2 - 2 := by linarith
  have h4 : (15 / 4 : ℝ) * cellA ^ 16 < 1 := by rw [cellA16]; norm_num
  nlinarith

/-- The two expressions for `Δₘ` agree (rationalization). -/
theorem DeltaM_eq_rationalized (hm : 8 ≤ m) :
    DeltaM m = 15 / 4 * cellA ^ (2 * m) /
      (2 * ((m / 2 - 2 : ℝ) + Real.sqrt ((m / 2 - 2 : ℝ) ^ 2 - 15 / 4 * cellA ^ (2 * m)))) := by
  have hd := disc_pos hm
  have h2 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  unfold DeltaM
  set d : ℝ := m / 2 - 2
  set s := Real.sqrt (d ^ 2 - 15 / 4 * cellA ^ (2 * m))
  have hs : s ^ 2 = d ^ 2 - 15 / 4 * cellA ^ (2 * m) := Real.sq_sqrt hd.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hpos : 0 < d + s := by have : (2:ℝ) ≤ d := by simp only [d]; linarith
                              linarith
  rw [eq_div_iff (by positivity)]
  nlinarith

/-- Bounds `0 < Δₘ ≤ (15/16) a¹⁶ < 1/4` for `m ≥ 8`. -/
theorem DeltaM_bounds (hm : 8 ≤ m) :
    0 < DeltaM m ∧ DeltaM m ≤ 15 / 16 * cellA ^ 16 ∧ 15 / 16 * cellA ^ 16 < 1 / 4 := by
  have hd := disc_pos hm
  have h2 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hA := cellA_pow_le hm
  have hA0 : 0 < cellA ^ (2 * m) := pow_pos cellA_pos _
  rw [DeltaM_eq_rationalized hm]
  set d : ℝ := m / 2 - 2
  have hd2 : (2:ℝ) ≤ d := by simp only [d]; linarith
  have hs0 : 0 ≤ Real.sqrt (d ^ 2 - 15 / 4 * cellA ^ (2 * m)) := Real.sqrt_nonneg _
  refine ⟨by positivity, ?_, by rw [cellA16]; norm_num⟩
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The relation `Δₘ (d - Δₘ) = bₘ cₘ` with `bₘ = (3/4)a^{m-2}`, `cₘ = (5/4)a^{m+2}`,
used to diagonalize `Bₘ`. -/
theorem DeltaM_relation (hm : 8 ≤ m) :
    DeltaM m * ((m / 2 - 2 : ℝ) - DeltaM m) =
      (3 / 4 * cellA ^ (m - 2)) * (5 / 4 * cellA ^ (m + 2)) := by
  have hd := disc_pos hm
  have hs : Real.sqrt ((m / 2 - 2 : ℝ) ^ 2 - 15 / 4 * cellA ^ (2 * m)) ^ 2 =
      (m / 2 - 2 : ℝ) ^ 2 - 15 / 4 * cellA ^ (2 * m) := Real.sq_sqrt hd.le
  have hp : cellA ^ (m - 2) * cellA ^ (m + 2) = cellA ^ (2 * m) := by
    rw [← pow_add]; congr 1; omega
  unfold DeltaM
  have : (3 / 4 * cellA ^ (m - 2)) * (5 / 4 * cellA ^ (m + 2)) =
      15 / 16 * cellA ^ (2 * m) := by rw [← hp]; ring
  rw [this]; nlinarith

/-- The characteristic polynomial of a `2 × 2` real matrix evaluated at `μ`. -/
def charEval (B : Matrix (Fin 2) (Fin 2) ℝ) (μ : ℝ) : ℝ :=
  (B 0 0 - μ) * (B 1 1 - μ) - B 0 1 * B 1 0

/-- For `m ≥ 8`, the eigenvalues of `Bₘ` are `5/4 - m/2 + Δₘ` and `-3/4 - Δₘ`; they are
real and distinct. -/
theorem Bmat_eigenvalues (hm : 8 ≤ m) :
    charEval (Bmat m) (5 / 4 - m / 2 + DeltaM m) = 0 ∧
      charEval (Bmat m) (-3 / 4 - DeltaM m) = 0 ∧
      (5 / 4 - m / 2 + DeltaM m : ℝ) ≠ -3 / 4 - DeltaM m := by
  have hrel := DeltaM_relation hm
  have hb := DeltaM_bounds hm
  have h2 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  refine ⟨?_, ?_, ?_⟩
  · simp only [charEval, Bmat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    nlinarith
  · simp only [charEval, Bmat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    nlinarith
  · intro h
    have : DeltaM m < 1 / 4 := lt_of_le_of_lt hb.2.1 hb.2.2
    linarith

/-- For `m ≥ 8` (an integer), the period multipliers of the two eigenvalues are
`-e^{i 4π Δₘ}` and `-e^{-i 4π Δₘ}`. -/
theorem period_multipliers_higher :
    Complex.exp (I * period * (5 / 4 - m / 2 + DeltaM m : ℝ)) =
        -Complex.exp (I * (4 * π * DeltaM m : ℝ)) ∧
      Complex.exp (I * period * (-3 / 4 - DeltaM m : ℝ)) =
        -Complex.exp (-(I * (4 * π * DeltaM m : ℝ))) := by
  have e1 : Complex.exp (I * (5 * π - 2 * π * m : ℝ)) = -1 := by
    convert exp_odd_pi_I (2 - (m : ℤ)) using 2; push_cast; ring
  have e2 : Complex.exp (I * (-(3 * π) : ℝ)) = -1 := by
    convert exp_odd_pi_I (-2) using 2; push_cast; ring
  unfold period
  constructor
  · rw [show I * ((4 * π : ℝ) : ℂ) * ((5 / 4 - m / 2 + DeltaM m : ℝ) : ℂ) =
      I * ((5 * π - 2 * π * m : ℝ) : ℂ) + I * ((4 * π * DeltaM m : ℝ) : ℂ) by push_cast; ring,
      Complex.exp_add, e1]; ring
  · rw [show I * ((4 * π : ℝ) : ℂ) * ((-3 / 4 - DeltaM m : ℝ) : ℂ) =
      I * ((-(3 * π) : ℝ) : ℂ) + -(I * ((4 * π * DeltaM m : ℝ) : ℂ)) by push_cast; ring,
      Complex.exp_add, e2]; ring

/-- None of the normal period multipliers equals `1`: their distances from `1` have the
common positive lower bound `2 cos(2π · (15/16) a¹⁶)`. -/
theorem multipliers_separated (hm : 8 ≤ m) (t : ℝ) (ht : t = DeltaM m ∨ t = -DeltaM m) :
    0 < 2 * Real.cos (2 * π * (15 / 16 * cellA ^ 16)) ∧
      2 * Real.cos (2 * π * (15 / 16 * cellA ^ 16)) ≤
        ‖-Complex.exp (I * (4 * π * t : ℝ)) - 1‖ := by
  have hb := DeltaM_bounds hm
  set c := 15 / 16 * cellA ^ 16 with hc
  have hc0 : 0 < c := by have := cellA_pos; positivity
  have hcpi : 2 * π * c < π / 2 := by nlinarith [Real.pi_pos]
  have habs : |t| ≤ c := by rcases ht with rfl | rfl <;> simp [abs_of_pos hb.1, hb.2.1]
  refine ⟨by
    have := Real.cos_pos_of_mem_Ioo (x := 2 * π * c) ⟨by nlinarith [Real.pi_pos], hcpi⟩
    linarith, ?_⟩
  -- ‖-e^{iθ} - 1‖ = ‖e^{iθ} + 1‖ = 2|cos(θ/2)|
  have hnorm : ‖-Complex.exp (I * (4 * π * t : ℝ)) - 1‖ = 2 * |Real.cos (2 * π * t)| := by
    have hc2 : ((2 * Real.cos (2 * π * t) : ℝ) : ℂ) =
        Complex.exp ((2 * π * t : ℝ) * I) + Complex.exp (-((2 * π * t : ℝ) : ℂ) * I) := by
      rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]; push_cast; ring
    have : -Complex.exp (I * (4 * π * t : ℝ)) - 1 =
        -(Complex.exp (I * (2 * π * t : ℝ)) *
          (2 * Real.cos (2 * π * t) : ℝ)) := by
      rw [hc2, mul_add, ← Complex.exp_add, ← Complex.exp_add]
      rw [show I * ((2 * π * t : ℝ) : ℂ) + -((2 * π * t : ℝ) : ℂ) * I = 0 by ring,
        Complex.exp_zero]
      push_cast; ring_nf
    rw [this, norm_neg, norm_mul, Complex.norm_exp, Complex.norm_real]
    simp [Real.norm_eq_abs]
  rw [hnorm]
  have hcos : Real.cos (2 * π * c) ≤ Real.cos (2 * π * |t|) := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
    exact mul_le_mul_of_nonneg_left habs (by positivity)
  have hcos_abs : Real.cos (2 * π * |t|) = Real.cos (2 * π * t) := by
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]; rw [mul_neg, Real.cos_neg]
  rw [hcos_abs] at hcos
  have := le_abs_self (Real.cos (2 * π * t))
  linarith

end higher

end Euler2D

end
