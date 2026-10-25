module

public import RequestProject.Euler.RadialStationary

/-!
# The physical velocity datum series

The terms are the actual centered velocity blocks
`(A_j r_j) • cellVelocity (r_j⁻¹ • (x - torusCenter))`.
The extra factor `r_j` is retained in every norm and summability estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set Filter Topology Metric
open scoped ENNReal

namespace Euler2D

/-- The actual `j`-th physical velocity block in the coordinate square. -/
def velocityDatumTerm (A₀ b R ρ : ℝ) (j : ℕ) (x : R2) : R2 :=
  (ampScale A₀ b j * radScale R ρ j) •
    cellVelocity ((radScale R ρ j)⁻¹ • (x - torusCenter))

lemma continuous_velocityDatumTerm (A₀ b R ρ : ℝ) (j : ℕ) :
    Continuous (velocityDatumTerm A₀ b R ρ j) := by
  unfold velocityDatumTerm
  simpa only [Pi.smul_def, Function.comp_def] using
    (continuous_cellVelocity.comp
      (by fun_prop : Continuous (fun x : R2 =>
        (radScale R ρ j)⁻¹ • (x - torusCenter)))).const_smul
          (ampScale A₀ b j * radScale R ρ j)

lemma radScale_pos {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (j : ℕ) :
    0 < radScale R ρ j := mul_pos hR (pow_pos hρ j)

lemma radScale_le_one {R ρ : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ) : radScale R ρ j ≤ 1 := by
  unfold radScale
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hρ.le hρ1) hR.le).trans
    (by simpa using hR1)

lemma velocityDatumTerm_eq_zero_of_radius_le {A₀ b R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (j : ℕ) {x : R2}
    (hx : radScale R ρ j ≤ ‖x - torusCenter‖) : velocityDatumTerm A₀ b R ρ j x = 0 := by
  have hr := radScale_pos hR hρ j
  have hscale : 1 ≤ ‖(radScale R ρ j)⁻¹ • (x - torusCenter)‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le]
    simpa only [inv_mul_cancel₀ hr.ne'] using
      mul_le_mul_of_nonneg_left hx (inv_pos.mpr hr).le
  rw [velocityDatumTerm, cellVelocity_eq_zero_of_one_le_norm hscale, smul_zero]

lemma support_velocityDatumTerm_subset_ball {A₀ b R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (j : ℕ) :
    Function.support (velocityDatumTerm A₀ b R ρ j) ⊆
      closedBall torusCenter (radScale R ρ j) := by
  intro x hx
  rw [mem_closedBall, dist_eq_norm]
  by_contra hn
  exact hx (velocityDatumTerm_eq_zero_of_radius_le hR hρ j (le_of_lt (lt_of_not_ge hn)))

lemma hasCompactSupport_velocityDatumTerm {A₀ b R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (j : ℕ) :
    HasCompactSupport (velocityDatumTerm A₀ b R ρ j) :=
  (isCompact_closedBall torusCenter (radScale R ρ j)).of_isClosed_subset
    (isClosed_tsupport _) (closure_minimal (support_velocityDatumTerm_subset_ball hR hρ j)
      isClosed_closedBall)

lemma velocityDatumTerm_memLp {A₀ b R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (p : ENNReal) (j : ℕ) : MemLp (velocityDatumTerm A₀ b R ρ j) p volume :=
  (continuous_velocityDatumTerm A₀ b R ρ j).memLp_of_hasCompactSupport
    (hasCompactSupport_velocityDatumTerm hR hρ j)

lemma velocityDatumTerm_memLp_torus {A₀ b R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (p : ENNReal) (j : ℕ) : MemLp (velocityDatumTerm A₀ b R ρ j) p μT :=
  (velocityDatumTerm_memLp hR hρ p j).mono_measure Measure.restrict_le_self

lemma support_velocityDatumTerm_subset_torusBox {A₀ b R ρ : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ) :
    Function.support (velocityDatumTerm A₀ b R ρ j) ⊆ torusBox := by
  intro x hx i
  have hn : ‖x - torusCenter‖ < radScale R ρ j := by
    by_contra hn
    exact hx (velocityDatumTerm_eq_zero_of_radius_le hR hρ j (le_of_not_gt hn))
  have hc : |x i - π| < 1 := by
    simpa only [PiLp.sub_apply, torusCenter_apply] using
      (abs_coord_le (x - torusCenter) i).trans_lt
        (hn.trans_le (radScale_le_one hR hR1 hρ hρ1 j))
  rw [abs_lt] at hc
  constructor <;> linarith [Real.pi_gt_three]

lemma eLpNorm_velocityDatumTerm_torus {A₀ b R ρ : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (j : ℕ) :
    eLpNorm (velocityDatumTerm A₀ b R ρ j) p μT =
      eLpNorm (velocityDatumTerm A₀ b R ρ j) p volume := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_torusBox.nullMeasurableSet]
  congr 1
  apply Set.indicator_eq_self.mpr
  exact support_velocityDatumTerm_subset_torusBox hR hR1 hρ hρ1 j

/-- The planar dilation identity with vector-valued profiles. -/
lemma eLpNorm_inv_smul_vector {E : Type*} [NormedAddCommGroup E]
    {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (f : R2 → E) :
    eLpNorm (fun x => f (r⁻¹ • x)) (ENNReal.ofReal q) volume =
      ENNReal.ofReal (r ^ (2 / q)) * eLpNorm f (ENNReal.ofReal q) volume := by
  let e : R2 ≃ᵐ R2 := (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne'))).toMeasurableEquiv
  have hmap := e.measurableEmbedding.eLpNorm_map_measure (g := f) (p := ENNReal.ofReal q)
    (μ := volume)
  change eLpNorm f (ENNReal.ofReal q) (Measure.map (fun x : R2 => r⁻¹ • x) volume) =
    eLpNorm (fun x => f (r⁻¹ • x)) (ENNReal.ofReal q) volume at hmap
  rw [← hmap, map_volume_inv_smul hr,
    eLpNorm_smul_measure_of_ne_zero
      (by positivity : ENNReal.ofReal (r ^ 2) ≠ 0) f (ENNReal.ofReal q) volume]
  simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hq.le, smul_eq_mul]
  congr 1
  rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg r) (inv_nonneg.mpr hq.le),
    ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
  congr 1

lemma eLpNorm_velocityDatumTerm_volume {A₀ b R ρ q : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ) (hq : 0 < q) (j : ℕ) :
    eLpNorm (velocityDatumTerm A₀ b R ρ j) (ENNReal.ofReal q) volume =
      ENNReal.ofReal (ampScale A₀ b j * radScale R ρ j * radScale R ρ j ^ (2 / q)) *
        eLpNorm cellVelocity (ENNReal.ofReal q) volume := by
  have hr := radScale_pos hR hρ j
  have hAr : 0 ≤ ampScale A₀ b j * radScale R ρ j :=
    mul_nonneg (div_nonneg hA (pow_pos hb j).le) hr.le
  have hmeas : AEStronglyMeasurable
      (fun y : R2 => cellVelocity ((radScale R ρ j)⁻¹ • y)) volume :=
    (continuous_cellVelocity.comp (by fun_prop)).aestronglyMeasurable
  change eLpNorm ((ampScale A₀ b j * radScale R ρ j) •
    ((fun y => cellVelocity ((radScale R ρ j)⁻¹ • y)) ∘ (fun x => x - torusCenter))) _ _ = _
  rw [eLpNorm_const_smul,
    eLpNorm_comp_measurePreserving hmeas (measurePreserving_sub_right volume torusCenter),
    eLpNorm_inv_smul_vector hr hq,
    ← ofReal_norm_eq_enorm, Real.norm_of_nonneg hAr, ← mul_assoc,
    ← ENNReal.ofReal_mul hAr]

lemma velocity_scale_geometric {A₀ b R ρ q : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (j : ℕ) :
    ampScale A₀ b j * radScale R ρ j * radScale R ρ j ^ (2 / q) =
      (A₀ * R ^ (1 + 2 / q)) * (ρ ^ (1 + 2 / q) / b) ^ j := by
  have hr := radScale_pos hR hρ j
  have hpow : radScale R ρ j * radScale R ρ j ^ (2 / q) = radScale R ρ j ^ (1 + 2 / q) := by
    rw [Real.rpow_add hr, Real.rpow_one]
  rw [mul_assoc, hpow]
  simp only [ampScale, radScale]
  have hj : (ρ ^ j) ^ (1 + 2 / q) = (ρ ^ (1 + 2 / q)) ^ j := by
    rw [← Real.rpow_natCast_mul hρ.le, mul_comm (j : ℝ), Real.rpow_mul_natCast hρ.le]
  rw [Real.mul_rpow hR.le (pow_nonneg hρ.le j), hj, div_pow]
  ring

/-- The physical block represented in an actual torus Lebesgue space. -/
def velocityDatumTermLp {A₀ b R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (p : ENNReal) (j : ℕ) : Lp R2 p μT :=
  (velocityDatumTerm_memLp_torus (A₀ := A₀) (b := b) hR hρ p j).toLp _

lemma coeFn_velocityDatumTermLp {A₀ b R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (p : ENNReal) (j : ℕ) :
    velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ p j =ᵐ[μT] velocityDatumTerm A₀ b R ρ j :=
  (velocityDatumTerm_memLp_torus hR hρ p j).coeFn_toLp

lemma norm_velocityDatumTermLp {A₀ b R ρ q : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q) (j : ℕ) :
    ‖velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ (ENNReal.ofReal q) j‖ =
      (eLpNorm cellVelocity (ENNReal.ofReal q) volume).toReal *
        (A₀ * R ^ (1 + 2 / q)) * (ρ ^ (1 + 2 / q) / b) ^ j := by
  rw [velocityDatumTermLp, Lp.norm_toLp, eLpNorm_velocityDatumTerm_torus hR hR1 hρ hρ1,
    eLpNorm_velocityDatumTerm_volume hA hb hR hρ hq,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by
      exact mul_nonneg (mul_nonneg (div_nonneg hA (pow_pos hb j).le)
        (radScale_pos hR hρ j).le) (Real.rpow_nonneg (radScale_pos hR hρ j).le _)),
    velocity_scale_geometric hR hρ]
  ring


lemma summable_norm_velocityDatumTermLp {A₀ b R ρ q : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q) (hsmall : ρ ^ (1 + 2 / q) < b) :
    Summable (fun j : ℕ =>
      ‖velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ (ENNReal.ofReal q) j‖) := by
  simp_rw [norm_velocityDatumTermLp hA hb hR hR1 hρ hρ1 hq]
  exact (summable_geometric_of_lt_one (by positivity) ((div_lt_one hb).mpr hsmall)).mul_left _

lemma summable_velocityDatumTermLp {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q) (hsmall : ρ ^ (1 + 2 / q) < b) :
    Summable (velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ (ENNReal.ofReal q)) :=
  (summable_norm_velocityDatumTermLp hA hb hR hR1 hρ hρ1 hq hsmall).of_norm

/-- The genuine physical velocity series in a torus Lebesgue space. -/
def velocityDatumLp {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hR : 0 < R) (hρ : 0 < ρ) : Lp R2 (ENNReal.ofReal q) μT :=
  ∑' j, velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ (ENNReal.ofReal q) j

lemma tendsto_sum_velocityDatumLp {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q) (hsmall : ρ ^ (1 + 2 / q) < b) :
    Tendsto (fun N => ∑ j ∈ Finset.range N,
      velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ (ENNReal.ofReal q) j) atTop
        (𝓝 (velocityDatumLp (A₀ := A₀) (b := b) (q := q) hR hρ)) :=
  (summable_velocityDatumTermLp hA hb hR hR1 hρ hρ1 hq hsmall).hasSum.tendsto_sum_nat

/-- A geometric error bound for the actual physical velocity series. -/
lemma norm_velocityDatumLp_sub_sum_le {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q) (hsmall : ρ ^ (1 + 2 / q) < b) (N : ℕ) :
    ‖velocityDatumLp (A₀ := A₀) (b := b) (q := q) hR hρ -
      ∑ j ∈ Finset.range N, velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ (ENNReal.ofReal q) j‖ ≤
      (eLpNorm cellVelocity (ENNReal.ofReal q) volume).toReal *
        (A₀ * R ^ (1 + 2 / q)) * (ρ ^ (1 + 2 / q) / b) ^ N /
          (1 - ρ ^ (1 + 2 / q) / b) := by
  let f := velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ (ENNReal.ofReal q)
  let κ : ℝ := ρ ^ (1 + 2 / q) / b
  have hκ0 : 0 ≤ κ := div_nonneg (Real.rpow_nonneg hρ.le _) hb.le
  have hκ1 : κ < 1 := (div_lt_one hb).mpr hsmall
  have hs := summable_velocityDatumTermLp hA hb hR hR1 hρ hρ1 hq hsmall
  have hn := (summable_nat_add_iff N).mpr
    (summable_norm_velocityDatumTermLp hA hb hR hR1 hρ hρ1 hq hsmall)
  have heq : velocityDatumLp (A₀ := A₀) (b := b) (q := q) hR hρ -
      ∑ j ∈ Finset.range N, f j = ∑' j, f (j + N) := by
    have hid := Summable.sum_add_tsum_nat_add N hs
    change ∑' j, f j - ∑ j ∈ Finset.range N, f j = _
    rw [← hid]
    abel
  rw [heq]
  calc
    ‖∑' j, f (j + N)‖ ≤ ∑' j, ‖f (j + N)‖ := norm_tsum_le_tsum_norm hn
    _ = ((eLpNorm cellVelocity (ENNReal.ofReal q) volume).toReal *
        (A₀ * R ^ (1 + 2 / q)) * κ ^ N) * ∑' j : ℕ, κ ^ j := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      dsimp only [f]
      rw [norm_velocityDatumTermLp hA hb hR hR1 hρ hρ1 hq, pow_add]
      dsimp only [κ]
      ring
    _ = _ := by rw [tsum_geometric_of_lt_one hκ0 hκ1]; rfl

/-- The physical datum in the actual `L²(𝕋²;ℝ²)` space. -/
def velocityDatumL2 {A₀ b R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) : L2T :=
  ∑' j, velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2 j

def velocityDatumPartialSumL2 {A₀ b R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (N : ℕ) : L2T :=
  ∑ j ∈ Finset.range N, velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2 j

lemma norm_velocityDatumTermLp_two {A₀ b R ρ : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ) :
    ‖velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2 j‖ =
      (eLpNorm cellVelocity 2 volume).toReal * (A₀ * R ^ 2) * (ρ ^ 2 / b) ^ j := by
  have hp : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have heq := norm_velocityDatumTermLp (q := 2) hA hb hR hR1 hρ hρ1 (by norm_num) j
  have hn : ‖velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ (ENNReal.ofReal (2 : ℝ)) j‖ =
      ‖velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2 j‖ := by
    simp only [velocityDatumTermLp, Lp.norm_toLp, hp]
  rw [hn] at heq
  norm_num [hp] at heq
  exact heq

lemma summable_norm_velocityDatumTermLp_two {A₀ b R ρ : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hsmall : ρ ^ 2 < b) :
    Summable (fun j : ℕ => ‖velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2 j‖) := by
  simp_rw [norm_velocityDatumTermLp_two hA hb hR hR1 hρ hρ1]
  exact (summable_geometric_of_lt_one (by positivity) ((div_lt_one hb).mpr hsmall)).mul_left _

lemma summable_velocityDatumTermLp_two {A₀ b R ρ : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hsmall : ρ ^ 2 < b) :
    Summable (velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2) :=
  (summable_norm_velocityDatumTermLp_two hA hb hR hR1 hρ hρ1 hsmall).of_norm
lemma tendsto_velocityDatumPartialSumL2 {A₀ b R ρ : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hsmall : ρ ^ 2 < b) :
    Tendsto (velocityDatumPartialSumL2 (A₀ := A₀) (b := b) hR hρ) atTop
      (𝓝 (velocityDatumL2 (A₀ := A₀) (b := b) hR hρ)) :=
  (summable_velocityDatumTermLp_two hA hb hR hR1 hρ hρ1 hsmall).hasSum.tendsto_sum_nat

lemma integral_velocityDatumTerm {A₀ b R ρ : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ) :
    ∫ x in torusBox, velocityDatumTerm A₀ b R ρ j x = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · unfold velocityDatumTerm
    rw [integral_smul, integral_sub_right_eq_self
      (fun y : R2 => cellVelocity ((radScale R ρ j)⁻¹ • y)) torusCenter,
      Measure.integral_comp_inv_smul_of_nonneg volume cellVelocity (radScale_pos hR hρ j).le,
      integral_cellVelocity, smul_zero, smul_zero]
  · intro x hx
    by_contra hn
    exact hx (support_velocityDatumTerm_subset_torusBox hR hR1 hρ hρ1 j hn)

lemma integral_velocityDatumTermLp_two {A₀ b R ρ : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ) :
    ∫ x in torusBox, velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2 j x = 0 :=
  (integral_congr_ae (coeFn_velocityDatumTermLp hR hρ 2 j)).trans
    (integral_velocityDatumTerm hR hR1 hρ hρ1 j)

lemma integral_velocityDatumPartialSumL2 {A₀ b R ρ : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ) :
    ∫ x in torusBox, velocityDatumPartialSumL2 (A₀ := A₀) (b := b) hR hρ N x = 0 := by
  induction N with
  | zero =>
      change (∫ x, (0 : L2T) x ∂μT) = 0
      exact (integral_congr_ae (Lp.coeFn_zero R2 2 μT)).trans (by simp)
  | succ N ih =>
      have hae := Lp.coeFn_add
        (velocityDatumPartialSumL2 (A₀ := A₀) (b := b) hR hρ N)
        (velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2 N)
      change (∫ x in torusBox, (∑ j ∈ Finset.range (N + 1),
        velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2 j) x) = 0
      rw [Finset.sum_range_succ]
      change (∫ x, (velocityDatumPartialSumL2 (A₀ := A₀) (b := b) hR hρ N +
        velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2 N) x ∂μT) = 0
      rw [integral_congr_ae hae]
      change (∫ x in torusBox, velocityDatumPartialSumL2 hR hρ N x +
        velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2 N x) = 0
      rw [integral_add ((Lp.memLp _).integrable (by norm_num))
        ((Lp.memLp _).integrable (by norm_num)), ih,
        integral_velocityDatumTermLp_two hR hR1 hρ hρ1]
      simp

/-- The actual strong-limit velocity datum has zero mean. -/
lemma integral_velocityDatumL2 {A₀ b R ρ : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hsmall : ρ ^ 2 < b) :
    ∫ x in torusBox, velocityDatumL2 (A₀ := A₀) (b := b) hR hρ x = 0 :=
  mean_zero_of_tendsto (Filter.Eventually.of_forall
    (integral_velocityDatumPartialSumL2 hR hR1 hρ hρ1))
      (tendsto_velocityDatumPartialSumL2 hA hb hR hR1 hρ hρ1 hsmall)



/-- The actual finite velocity sum has this continuous angular profile. -/
def velocityDatumProfile (A₀ b R ρ : ℝ) (N : ℕ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, ampScale A₀ b j * cellOmegaSq (s / radScale R ρ j ^ 2)

lemma continuous_velocityDatumProfile (A₀ b R ρ : ℝ) (N : ℕ) :
    Continuous (velocityDatumProfile A₀ b R ρ N) := by
  unfold velocityDatumProfile
  apply continuous_finset_sum
  intro j hj
  exact continuous_const.mul (continuous_cellOmegaSq.comp (continuous_id.div_const _))

lemma velocityDatumTerm_eq_radial {A₀ b R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (j : ℕ) (x : R2) :
    velocityDatumTerm A₀ b R ρ j x =
      (ampScale A₀ b j * cellOmegaSq (‖x - torusCenter‖ ^ 2 / radScale R ρ j ^ 2)) •
        perpJ (x - torusCenter) := by
  have hr := radScale_pos hR hρ j
  change scaledCellVelocity (ampScale A₀ b j) (radScale R ρ j) (x - torusCenter) = _
  rw [scaledCellVelocity_eq hr, cellOmega_eq_sq _
    (mul_nonneg (inv_nonneg.mpr hr.le) (norm_nonneg _))]
  have hs : ((radScale R ρ j)⁻¹ * ‖x - torusCenter‖) ^ 2 =
      ‖x - torusCenter‖ ^ 2 / radScale R ρ j ^ 2 := by
    rw [mul_pow, inv_pow]
    ring
  rw [hs]

lemma sum_velocityDatumTerm_eq_radial {A₀ b R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (N : ℕ) (x : R2) :
    (∑ j ∈ Finset.range N, velocityDatumTerm A₀ b R ρ j x) =
      radialVelocity (velocityDatumProfile A₀ b R ρ N) torusCenter x := by
  simp only [velocityDatumTerm_eq_radial hR hρ, radialVelocity, velocityDatumProfile,
    Finset.sum_smul]

lemma velocityDatumProfile_eq_zero {A₀ b R ρ : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N : ℕ) (s : ℝ) (hs : 1 ≤ s) : velocityDatumProfile A₀ b R ρ N s = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have hr := radScale_pos hR hρ j
  have hr1 := radScale_le_one hR hR1 hρ hρ1 j
  have hdiv : 1 ≤ s / radScale R ρ j ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hr)]
    nlinarith
  rw [cellOmegaSq_eq_zero_of_one_le _ hdiv, mul_zero]

lemma coeFn_velocityDatumPartialSumL2 {A₀ b R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (N : ℕ) :
    velocityDatumPartialSumL2 (A₀ := A₀) (b := b) hR hρ N =ᵐ[μT]
      fun x => ∑ j ∈ Finset.range N, velocityDatumTerm A₀ b R ρ j x := by
  induction N with
  | zero => simpa [velocityDatumPartialSumL2, Pi.zero_def] using Lp.coeFn_zero R2 2 μT
  | succ N ih =>
      have hadd := Lp.coeFn_add
        (velocityDatumPartialSumL2 (A₀ := A₀) (b := b) hR hρ N)
        (velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2 N)
      filter_upwards [hadd, ih, coeFn_velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2 N]
        with x ha hi ht
      change ((∑ j ∈ Finset.range (N + 1),
        velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2 j) : L2T) x = _
      rw [Finset.sum_range_succ]
      change (velocityDatumPartialSumL2 (A₀ := A₀) (b := b) hR hρ N +
        velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2 N) x = _
      rw [ha]
      change velocityDatumPartialSumL2 (A₀ := A₀) (b := b) hR hρ N x +
        velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2 N x = _
      rw [hi, ht, Finset.sum_range_succ]

lemma coeFn_velocityDatumPartialSumL2_radial {A₀ b R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (N : ℕ) :
    velocityDatumPartialSumL2 (A₀ := A₀) (b := b) hR hρ N =ᵐ[μT]
      radialVelocity (velocityDatumProfile A₀ b R ρ N) torusCenter := by
  filter_upwards [coeFn_velocityDatumPartialSumL2 (A₀ := A₀) (b := b) hR hρ N] with x hx
  rw [hx, sum_velocityDatumTerm_eq_radial hR hρ]

lemma isStationary_velocityDatumPartialSumL2 {A₀ b R ρ : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ) :
    IsStationary (velocityDatumPartialSumL2 (A₀ := A₀) (b := b) hR hρ N) :=
  isStationary_of_continuous_radialProfile (continuous_velocityDatumProfile A₀ b R ρ N)
    (velocityDatumProfile_eq_zero hR hR1 hρ hρ1 N)
    (coeFn_velocityDatumPartialSumL2_radial hR hρ N)

lemma divFree_velocityDatumPartialSumL2 {A₀ b R ρ : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ) :
    DivFree (velocityDatumPartialSumL2 (A₀ := A₀) (b := b) hR hρ N) :=
  divFree_of_continuous_radialProfile (continuous_velocityDatumProfile A₀ b R ρ N)
    (velocityDatumProfile_eq_zero hR hR1 hρ hρ1 N)
    (coeFn_velocityDatumPartialSumL2_radial hR hρ N)

/-- The strong-limit physical velocity datum is stationary. -/
lemma isStationary_velocityDatumL2 {A₀ b R ρ : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hsmall : ρ ^ 2 < b) :
    IsStationary (velocityDatumL2 (A₀ := A₀) (b := b) hR hρ) :=
  IsStationary.of_tendsto (Filter.Eventually.of_forall
    (isStationary_velocityDatumPartialSumL2 hR hR1 hρ hρ1))
      (tendsto_velocityDatumPartialSumL2 hA hb hR hR1 hρ hρ1 hsmall)

/-- The same actual datum is distributionally divergence free. -/
lemma divFree_velocityDatumL2 {A₀ b R ρ : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hsmall : ρ ^ 2 < b) :
    DivFree (velocityDatumL2 (A₀ := A₀) (b := b) hR hρ) :=
  divFree_of_tendsto (tendsto_velocityDatumPartialSumL2 hA hb hR hR1 hρ hρ1 hsmall)
    (Filter.Eventually.of_forall (divFree_velocityDatumPartialSumL2 hR hR1 hρ hρ1))

/-- The vorticity summability condition in the paper implies velocity summability. -/
lemma velocity_small_of_vorticity_small {ρ b q : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hsmall : ρ ^ (2 / q) < b) :
    ρ ^ (1 + 2 / q) < b := by
  rw [Real.rpow_add hρ, Real.rpow_one]
  exact (mul_le_of_le_one_left (Real.rpow_nonneg hρ.le _) hρ1).trans_lt hsmall

lemma velocity_two_small_of_vorticity_small {ρ b q : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 1 ≤ q) (hsmall : ρ ^ (2 / q) < b) :
    ρ ^ 2 < b := by
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hexp : 2 / q ≤ 2 := (div_le_iff₀ hqpos).mpr (by linarith)
  have hbound := Real.rpow_le_rpow_of_exponent_ge hρ hρ1 hexp
  have hbound' : ρ ^ 2 ≤ ρ ^ (2 / q) := by simpa only [Real.rpow_two] using hbound
  exact hbound'.trans_lt hsmall

lemma norm_velocityDatumL2_sub_partial_le {A₀ b R ρ : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hsmall : ρ ^ 2 < b) (N : ℕ) :
    ‖velocityDatumL2 (A₀ := A₀) (b := b) hR hρ -
      velocityDatumPartialSumL2 (A₀ := A₀) (b := b) hR hρ N‖ ≤
      (eLpNorm cellVelocity 2 volume).toReal * (A₀ * R ^ 2) * (ρ ^ 2 / b) ^ N /
        (1 - ρ ^ 2 / b) := by
  let f := velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ 2
  let κ : ℝ := ρ ^ 2 / b
  have hκ0 : 0 ≤ κ := by positivity
  have hκ1 : κ < 1 := (div_lt_one hb).mpr hsmall
  have hs := summable_velocityDatumTermLp_two hA hb hR hR1 hρ hρ1 hsmall
  have hn := (summable_nat_add_iff N).mpr
    (summable_norm_velocityDatumTermLp_two hA hb hR hR1 hρ hρ1 hsmall)
  have heq : velocityDatumL2 (A₀ := A₀) (b := b) hR hρ -
      velocityDatumPartialSumL2 (A₀ := A₀) (b := b) hR hρ N = ∑' j, f (j + N) := by
    have hid := Summable.sum_add_tsum_nat_add N hs
    change ∑' j, f j - ∑ j ∈ Finset.range N, f j = _
    rw [← hid]
    abel
  rw [heq]
  calc
    ‖∑' j, f (j + N)‖ ≤ ∑' j, ‖f (j + N)‖ := norm_tsum_le_tsum_norm hn
    _ = ((eLpNorm cellVelocity 2 volume).toReal * (A₀ * R ^ 2) * κ ^ N) *
        ∑' j : ℕ, κ ^ j := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      dsimp only [f]
      rw [norm_velocityDatumTermLp_two hA hb hR hR1 hρ hρ1, pow_add]
      dsimp only [κ]
      ring
    _ = _ := by rw [tsum_geometric_of_lt_one hκ0 hκ1]; rfl
lemma norm_velocityDatumL2_le {A₀ b R ρ : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hsmall : ρ ^ 2 < b) :
    ‖velocityDatumL2 (A₀ := A₀) (b := b) hR hρ‖ ≤
      (eLpNorm cellVelocity 2 volume).toReal * (A₀ * R ^ 2) / (1 - ρ ^ 2 / b) := by
  simpa [velocityDatumPartialSumL2] using
    norm_velocityDatumL2_sub_partial_le hA hb hR hR1 hρ hρ1 hsmall 0



lemma coeFn_sum_velocityDatumTermLp {A₀ b R ρ : ℝ} {p : ENNReal} [Fact (1 ≤ p)]
    (hR : 0 < R) (hρ : 0 < ρ) (N : ℕ) :
    ((∑ j ∈ Finset.range N, velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ p j) : Lp R2 p μT)
      =ᵐ[μT] fun x => ∑ j ∈ Finset.range N, velocityDatumTerm A₀ b R ρ j x := by
  induction N with
  | zero => simpa [Pi.zero_def] using Lp.coeFn_zero R2 p μT
  | succ N ih =>
      have hadd := Lp.coeFn_add
        (∑ j ∈ Finset.range N, velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ p j)
        (velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ p N)
      filter_upwards [hadd, ih, coeFn_velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ p N]
        with x ha hi ht
      rw [Finset.sum_range_succ, ha]
      change (∑ j ∈ Finset.range N, velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ p j) x +
        velocityDatumTermLp (A₀ := A₀) (b := b) hR hρ p N x = _
      rw [hi, ht, Finset.sum_range_succ]

/-- The Lebesgue-space sums at different exponents represent the same
physical velocity datum, by uniqueness of limits in measure. -/
lemma velocityDatumLp_ae_velocityDatumL2 {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q)
    (hsmall : ρ ^ (1 + 2 / q) < b) (hsmall2 : ρ ^ 2 < b) :
    velocityDatumLp (A₀ := A₀) (b := b) (q := q) hR hρ =ᵐ[μT]
      velocityDatumL2 (A₀ := A₀) (b := b) hR hρ := by
  have hqmeas := tendstoInMeasure_of_tendsto_Lp
    (tendsto_sum_velocityDatumLp hA hb hR hR1 hρ hρ1 hq hsmall)
  have h2meas := tendstoInMeasure_of_tendsto_Lp
    (tendsto_velocityDatumPartialSumL2 hA hb hR hR1 hρ hρ1 hsmall2)
  have hqactual : TendstoInMeasure μT
      (fun N x => ∑ j ∈ Finset.range N, velocityDatumTerm A₀ b R ρ j x) atTop
        (velocityDatumLp (A₀ := A₀) (b := b) (q := q) hR hρ) :=
    hqmeas.congr (coeFn_sum_velocityDatumTermLp hR hρ) Filter.EventuallyEq.rfl
  have h2actual : TendstoInMeasure μT
      (fun N x => ∑ j ∈ Finset.range N, velocityDatumTerm A₀ b R ρ j x) atTop
        (velocityDatumL2 (A₀ := A₀) (b := b) hR hρ) :=
    h2meas.congr (coeFn_velocityDatumPartialSumL2 hR hρ) Filter.EventuallyEq.rfl
  exact tendstoInMeasure_ae_unique hqactual h2actual

/-- In particular, the actual `L²` stationary datum itself belongs to `L^q`
under the original vorticity summability condition from the paper. -/
lemma velocityDatumL2_memLp_of_vorticity_condition {A₀ b R ρ q : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 1 ≤ q) (hsmall : ρ ^ (2 / q) < b) :
    MemLp (velocityDatumL2 (A₀ := A₀) (b := b) hR hρ) (ENNReal.ofReal q) μT := by
  letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq⟩
  exact (Lp.memLp (velocityDatumLp (A₀ := A₀) (b := b) (q := q) hR hρ)).ae_eq
    (velocityDatumLp_ae_velocityDatumL2 hA hb hR hR1 hρ hρ1 (zero_lt_one.trans_le hq)
      (velocity_small_of_vorticity_small hρ hρ1 hsmall)
      (velocity_two_small_of_vorticity_small hρ hρ1 hq hsmall))

lemma norm_velocityDatumLp_le {A₀ b R ρ q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q) (hsmall : ρ ^ (1 + 2 / q) < b) :
    ‖velocityDatumLp (A₀ := A₀) (b := b) (q := q) hR hρ‖ ≤
      (eLpNorm cellVelocity (ENNReal.ofReal q) volume).toReal *
        (A₀ * R ^ (1 + 2 / q)) / (1 - ρ ^ (1 + 2 / q) / b) := by
  simpa using norm_velocityDatumLp_sub_sum_le hA hb hR hR1 hρ hρ1 hq hsmall 0

lemma norm_velocityDatumL2_Lq_le {A₀ b R ρ q : ℝ}
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 1 ≤ q) (hsmall : ρ ^ (2 / q) < b) :
    (eLpNorm (velocityDatumL2 (A₀ := A₀) (b := b) hR hρ) (ENNReal.ofReal q) μT).toReal ≤
      (eLpNorm cellVelocity (ENNReal.ofReal q) volume).toReal *
        (A₀ * R ^ (1 + 2 / q)) / (1 - ρ ^ (1 + 2 / q) / b) := by
  letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr hq⟩
  have hs := velocity_small_of_vorticity_small hρ hρ1 hsmall
  have heq := velocityDatumLp_ae_velocityDatumL2 hA hb hR hR1 hρ hρ1
    (zero_lt_one.trans_le hq) hs (velocity_two_small_of_vorticity_small hρ hρ1 hq hsmall)
  rw [← eLpNorm_congr_ae heq]
  exact norm_velocityDatumLp_le hA hb hR hR1 hρ hρ1 (zero_lt_one.trans_le hq) hs


end Euler2D

end







