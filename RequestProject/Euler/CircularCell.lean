module

public import RequestProject.Euler.NormalEigen
public import RequestProject.Euler.Basic

/-!
# The circular two-interface cell

Formalization of the following statements of the paper:

* Lemma `bv:two-interface-norms` (norms of a two-interface label),
* Definition `def:circular-cell` (the circular two-interface vorticity `W`),
* the circulation computation in Lemma `bv:circular-velocity` and Lemma `pc:circular-period`
  (angular velocities `Ω(r) = (2πr²)⁻¹ ∫_{B_r} W`, the interface values `1/2` and `0`, and the
  common period `P = 4π`),
* the scaling identity of Lemma `bv:circular-velocity` for the planar Biot–Savart law
  (Definition `def:kernel`).
-/

@[expose] public section

open MeasureTheory Real Metric

namespace Euler2D

/-! ### Norms of a two-interface label -/

section TwoInterface

variable {D₁ D₂ : Set R2}

lemma integrable_indicator_const {s : Set R2} (hs : MeasurableSet s) (hf : volume s ≠ ⊤)
    (c : ℝ) : Integrable (s.indicator fun _ => c) :=
  (integrableOn_const hf).integrable_indicator hs

/-- The two-interface label `ω = (5/2) 1_{D₁} - (3/2) 1_{D₂}`. -/
noncomputable def twoInterface (D₁ D₂ : Set R2) (x : R2) : ℝ :=
  D₁.indicator (fun _ => (5 / 2 : ℝ)) x - D₂.indicator (fun _ => (3 / 2 : ℝ)) x

lemma abs_twoInterface (h : D₁ ⊆ D₂) (x : R2) :
    |twoInterface D₁ D₂ x| =
      D₁.indicator (fun _ => (1 : ℝ)) x + (D₂ \ D₁).indicator (fun _ => (3 / 2 : ℝ)) x := by
  unfold twoInterface
  by_cases h1 : x ∈ D₁
  · have h2 : x ∈ D₂ := h h1
    simp [h1, h2]; norm_num
  · by_cases h2 : x ∈ D₂
    · simp [h1, h2]; norm_num
    · simp [h1, h2]

/-- **Lemma (Norms of a two-interface label).** If `D₁ ⊆ D₂` have areas `3π/5` and `π`, then
`ω = (5/2)1_{D₁} - (3/2)1_{D₂}` has `∫ ω = 0` and `‖ω‖₁ = 6π/5`. -/
theorem twoInterface_integral (h : D₁ ⊆ D₂) (hD₁ : MeasurableSet D₁) (hD₂ : MeasurableSet D₂)
    (hv₁ : volume D₁ = ENNReal.ofReal (3 * π / 5)) (hv₂ : volume D₂ = ENNReal.ofReal π) :
    ∫ x, twoInterface D₁ D₂ x = 0 ∧ ∫ x, |twoInterface D₁ D₂ x| = 6 * π / 5 := by
  have f₁ : volume D₁ ≠ ⊤ := by rw [hv₁]; exact ENNReal.ofReal_ne_top
  have f₂ : volume D₂ ≠ ⊤ := by rw [hv₂]; exact ENNReal.ofReal_ne_top
  have r₁ : volume.real D₁ = 3 * π / 5 := by
    rw [measureReal_def, hv₁, ENNReal.toReal_ofReal (by positivity)]
  have r₂ : volume.real D₂ = π := by
    rw [measureReal_def, hv₂, ENNReal.toReal_ofReal (by positivity)]
  have i₁ := integrable_indicator_const hD₁ f₁ (5 / 2)
  have i₂ := integrable_indicator_const hD₂ f₂ (3 / 2)
  constructor
  · unfold twoInterface
    rw [integral_sub i₁ i₂, integral_indicator_const _ hD₁, integral_indicator_const _ hD₂,
      r₁, r₂]
    simp; ring
  · simp_rw [abs_twoInterface h]
    have f₃ : volume (D₂ \ D₁) ≠ ⊤ := measure_ne_top_of_subset Set.diff_subset f₂
    rw [integral_add (integrable_indicator_const hD₁ f₁ 1)
        (integrable_indicator_const (hD₂.diff hD₁) f₃ (3 / 2)),
      integral_indicator_const _ hD₁, integral_indicator_const _ (hD₂.diff hD₁),
      measureReal_diff h hD₁ f₂, r₁, r₂]
    simp; ring

/-- **Lemma (Norms of a two-interface label), `L^∞` part.** `‖ω‖_∞ = 3/2`. -/
theorem twoInterface_eLpNorm_top (h : D₁ ⊆ D₂) (hD₁ : MeasurableSet D₁)
    (hD₂ : MeasurableSet D₂)
    (hv₁ : volume D₁ = ENNReal.ofReal (3 * π / 5)) (hv₂ : volume D₂ = ENNReal.ofReal π) :
    eLpNorm (twoInterface D₁ D₂) ⊤ volume = ENNReal.ofReal (3 / 2) := by
  have hbound : ∀ x, ‖twoInterface D₁ D₂ x‖ ≤ 3 / 2 := by
    intro x
    rw [Real.norm_eq_abs, abs_twoInterface h]
    by_cases h1 : x ∈ D₁
    · simp [h1]; norm_num
    · by_cases h2 : x ∈ D₂ <;> norm_num [h1, h2]
  have hpos : volume (D₂ \ D₁) ≠ 0 := by
    have f₁ : volume D₁ ≠ ⊤ := by rw [hv₁]; exact ENNReal.ofReal_ne_top
    rw [measure_diff h hD₁.nullMeasurableSet f₁, hv₁, hv₂, ← ENNReal.ofReal_sub _ (by positivity)]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    nlinarith [Real.pi_pos]
  have hmeas : AEStronglyMeasurable (twoInterface D₁ D₂) volume :=
    ((stronglyMeasurable_const.indicator hD₁).sub
      (stronglyMeasurable_const.indicator hD₂)).aestronglyMeasurable
  rw [eLpNorm_exponent_top hmeas]
  apply le_antisymm
  · exact eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hbound)
  · by_contra hlt
    push_neg at hlt
    have hae := ae_lt_of_essSup_lt (f := fun x => ‖twoInterface D₁ D₂ x‖ₑ) hlt
    have : ∀ᵐ x ∂volume, x ∉ D₂ \ D₁ := by
      filter_upwards [hae] with x hx hmem
      have hval : ‖twoInterface D₁ D₂ x‖ₑ = ENNReal.ofReal (3 / 2) := by
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_twoInterface h]
        simp [hmem.2, hmem]
      exact (lt_irrefl _ (hval ▸ hx))
    exact hpos (measure_eq_zero_iff_ae_notMem.mpr this)

end TwoInterface

/-! ### The circular cell `W` and its angular velocity -/

/-- **Definition (Circular two-interface vorticity).**
`W = (5/2) 1_{B_a} - (3/2) 1_{B_1}` with `a = √(3/5)`. -/
noncomputable def cellW : R2 → ℝ := twoInterface (ball 0 cellA) (ball 0 1)

/-- The angular velocity profile `Ω(r)` of `K * W`. -/
noncomputable def cellOmega (r : ℝ) : ℝ :=
  if r ≤ cellA then 1 / 2 else if r < 1 then 3 * (1 - r ^ 2) / (4 * r ^ 2) else 0

lemma volReal_ball (r : ℝ) (hr : 0 ≤ r) : volume.real (ball (0 : R2) r) = π * r ^ 2 := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal Real.pi_pos.le]
  ring

lemma ball_inter_ball {r s : ℝ} : ball (0 : R2) r ∩ ball 0 s = ball 0 (min r s) := by
  ext x; simp

/-- The mass of `W` in the disk `B_r`. -/
theorem cellW_mass (r : ℝ) (hr : 0 ≤ r) :
    ∫ x in ball (0 : R2) r, cellW x =
      if r ≤ cellA then π * r ^ 2 else if r < 1 then 3 * π / 2 * (1 - r ^ 2) else 0 := by
  have ha := cellA_pos
  have ha1 := cellA_lt_one
  have ha2 := cellA_sq
  have fin : ∀ s : ℝ, volume (ball (0 : R2) s) ≠ ⊤ := fun s => measure_ball_lt_top.ne
  unfold cellW twoInterface
  rw [integral_sub (integrable_indicator_const measurableSet_ball (fin _) _).integrableOn
    (integrable_indicator_const measurableSet_ball (fin _) _).integrableOn,
    setIntegral_indicator measurableSet_ball, setIntegral_indicator measurableSet_ball,
    setIntegral_const, setIntegral_const, ball_inter_ball, ball_inter_ball,
    volReal_ball _ (le_min hr ha.le), volReal_ball _ (le_min hr zero_le_one)]
  simp only [smul_eq_mul]
  split_ifs with h1 h2
  · rw [min_eq_left h1, min_eq_left (h1.trans ha1.le)]; ring
  · rw [min_eq_right (not_le.mp h1).le, min_eq_left h2.le, ha2]; ring
  · rw [min_eq_right (not_le.mp h1).le, min_eq_right (not_lt.mp h2), ha2]; ring

/-- **Lemma (Velocity of the circular cell), circulation form.** The angular velocity
`(2πr²)⁻¹ ∫_{B_r} W` of `K * W` on the circle of radius `r > 0` is `Ω(r)`. -/
theorem cellW_angular_velocity (r : ℝ) (hr : 0 < r) :
    (2 * π * r ^ 2)⁻¹ * ∫ x in ball (0 : R2) r, cellW x = cellOmega r := by
  rw [cellW_mass r hr.le, cellOmega]
  have hpi := Real.pi_pos
  split_ifs <;> field_simp <;> ring

/-- The angular velocities at the two interfaces are `Ω₁ = Ω(a) = 1/2` and `Ω₂ = Ω(1) = 0`;
`Ω` is continuous at the inner interface; `Ω` vanishes outside the unit disk. -/
theorem cellOmega_interfaces :
    cellOmega cellA = 1 / 2 ∧ cellOmega 1 = 0 ∧
      3 * (1 - cellA ^ 2) / (4 * cellA ^ 2) = 1 / 2 ∧ ∀ r, 1 ≤ r → cellOmega r = 0 := by
  have ha1 := cellA_lt_one
  refine ⟨by simp [cellOmega], by simp [cellOmega, not_le.mpr ha1], by rw [cellA_sq]; norm_num,
    fun r hr => ?_⟩
  simp [cellOmega, not_le.mpr (ha1.trans_le hr), not_lt.mpr hr]

/-- **Lemma (The circular trajectory).** The material contours `dⱼ e^{i(θ + Ωⱼ t)}` with
`Ω₁ = 1/2`, `Ω₂ = 0` return to themselves at the common period `P = 4π`. -/
theorem circular_period (θ : ℝ) :
    Complex.exp (Complex.I * (θ + cellOmega cellA * period)) = Complex.exp (Complex.I * θ) ∧
      Complex.exp (Complex.I * (θ + cellOmega 1 * period)) = Complex.exp (Complex.I * θ) := by
  obtain ⟨h1, h2, -, -⟩ := cellOmega_interfaces
  rw [h1, h2, period]
  refine ⟨?_, by simp⟩
  rw [show Complex.I * (θ + ((1 / 2 : ℝ) : ℂ) * ((4 * π : ℝ) : ℂ)) =
      Complex.I * θ + ((1 : ℤ) : ℂ) * (2 * π * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ### The planar Biot–Savart law and the scaling identity -/

/-- `J x = x^⊥ = (-x₂, x₁)`. -/
noncomputable def perpJ (x : R2) : R2 := !₂[-x 1, x 0]

/-- The planar Biot–Savart kernel `K(x) = J x / (2π|x|²)`. -/
noncomputable def kernelK (x : R2) : R2 := (2 * π * ‖x‖ ^ 2)⁻¹ • perpJ x

/-- The planar Biot–Savart velocity `(K * f)(x) = ∫ K(x - y) f(y) dy`. -/
noncomputable def biotSavart (f : R2 → ℝ) (x : R2) : R2 := ∫ y, f y • kernelK (x - y)

lemma perpJ_smul (c : ℝ) (x : R2) : perpJ (c • x) = c • perpJ x := by
  ext i; fin_cases i <;> simp [perpJ]

lemma kernelK_smul {c : ℝ} (hc : 0 < c) (x : R2) : kernelK (c • x) = c⁻¹ • kernelK x := by
  unfold kernelK
  rw [perpJ_smul, smul_smul, smul_smul, norm_smul, Real.norm_of_nonneg hc.le]
  congr 1
  rcases eq_or_ne ‖x‖ 0 with h | h
  · simp [h]
  · field_simp

/-- **Scaling identity (Lemma `bv:circular-velocity`).** The velocity of a scaled copy
`A f(x/r₀)` is `A r₀ (K*f)(x/r₀)`. -/
theorem biotSavart_scale (f : R2 → ℝ) (A r₀ : ℝ) (hr₀ : 0 < r₀) (x : R2) :
    biotSavart (fun y => A * f (r₀⁻¹ • y)) x = (A * r₀) • biotSavart f (r₀⁻¹ • x) := by
  unfold biotSavart
  set g : R2 → R2 := fun z => (A * r₀⁻¹) • (f z • kernelK (r₀⁻¹ • x - z)) with hg
  have key : (fun y : R2 => (A * f (r₀⁻¹ • y)) • kernelK (x - y)) = fun y => g (r₀⁻¹ • y) := by
    funext y
    have : x - y = r₀ • (r₀⁻¹ • x - r₀⁻¹ • y) := by
      rw [smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hr₀.ne', one_smul, one_smul]
    rw [this, kernelK_smul hr₀, smul_smul, hg]
    simp only [smul_smul]
    congr 1; ring
  rw [key, Measure.integral_comp_inv_smul_of_nonneg volume g hr₀.le, hg, integral_smul,
    smul_smul]
  congr 1
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  field_simp

end Euler2D

end
