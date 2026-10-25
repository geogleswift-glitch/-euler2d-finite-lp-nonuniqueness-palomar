module

public import RequestProject.Euler.ContourHolderAlgebra

/-!
# Actual Hölder-norm continuity of inversion and boundary phases

The inverse-difference identity is an equality of actual Hölder functions.
The bounded pointwise product gives its norm estimate.  This proves genuine
inverse convergence under a common positive pointwise lower bound, and a
uniform Lipschitz estimate when the Hölder norms also have a common bound.
The actual phase `conj g / g` is continuous in the same Hölder norm.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal BoundedContinuousFunction ComplexConjugate

namespace Euler2D.HolderFunctionSpace

variable {X : Type*} [MetricSpace X] {γ : ℝ≥0}

theorem sub_inverseOfNormLower_eq (f g : HolderFunctionSpace X ℂ γ)
    {c : ℝ} (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) (hg : ∀ x, c ≤ ‖g x‖) :
    inverseOfNormLower f hc hf - inverseOfNormLower g hc hg =
      pointwiseMul (pointwiseMul (g - f) (inverseOfNormLower f hc hf))
        (inverseOfNormLower g hc hg) := by
  apply HolderFunctionSpace.ext
  intro x
  change (f x)⁻¹ - (g x)⁻¹ = ((g x - f x) * (f x)⁻¹) * (g x)⁻¹
  have hnf : f x ≠ 0 := norm_pos_iff.mp (hc.trans_le (hf x))
  have hng : g x ≠ 0 := norm_pos_iff.mp (hc.trans_le (hg x))
  rw [inv_sub_inv' hnf hng]
  ring

/-- The actual inverse-difference norm bound, with the genuine max-norm
product constant accounted for twice. -/
theorem norm_sub_inverseOfNormLower_le (f g : HolderFunctionSpace X ℂ γ)
    {c : ℝ} (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) (hg : ∀ x, c ≤ ‖g x‖) :
    ‖inverseOfNormLower f hc hf - inverseOfNormLower g hc hg‖ ≤
      4 * ‖f - g‖ * ‖inverseOfNormLower f hc hf‖ * ‖inverseOfNormLower g hc hg‖ := by
  rw [sub_inverseOfNormLower_eq f g hc hf hg]
  calc
    _ ≤ 2 * ‖pointwiseMul (g - f) (inverseOfNormLower f hc hf)‖ *
        ‖inverseOfNormLower g hc hg‖ := norm_pointwiseMul_le _ _
    _ ≤ 2 * (2 * ‖g - f‖ * ‖inverseOfNormLower f hc hf‖) *
        ‖inverseOfNormLower g hc hg‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_pointwiseMul_le _ _) (by norm_num)) (norm_nonneg _)
    _ = _ := by rw [norm_sub_rev g f]; ring

def inverseBound (c M : ℝ) : ℝ := max c⁻¹ (M / c ^ 2)

lemma inverseBound_pos {c : ℝ} (hc : 0 < c) (M : ℝ) : 0 < inverseBound c M :=
  (inv_pos.mpr hc).trans_le (le_max_left _ _)

lemma norm_inverseOfNormLower_le_uniform (f : HolderFunctionSpace X ℂ γ)
    {c M : ℝ} (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) (hM : ‖f‖ ≤ M) :
    ‖inverseOfNormLower f hc hf‖ ≤ inverseBound c M :=
  (norm_inverseOfNormLower_le f hc hf).trans
    (max_le_max_left _ (div_le_div_of_nonneg_right hM (sq_nonneg c)))

theorem norm_sub_inverseOfNormLower_le_uniform (f g : HolderFunctionSpace X ℂ γ)
    {c M : ℝ} (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) (hg : ∀ x, c ≤ ‖g x‖)
    (hfM : ‖f‖ ≤ M) (hgM : ‖g‖ ≤ M) :
    ‖inverseOfNormLower f hc hf - inverseOfNormLower g hc hg‖ ≤
      (4 * (inverseBound c M) ^ 2) * ‖f - g‖ := by
  have hB := (inverseBound_pos hc M).le
  have hA : 0 ≤ 4 * ‖f - g‖ := mul_nonneg (by norm_num) (norm_nonneg _)
  calc
    _ ≤ 4 * ‖f - g‖ * ‖inverseOfNormLower f hc hf‖ *
        ‖inverseOfNormLower g hc hg‖ := norm_sub_inverseOfNormLower_le f g hc hf hg
    _ ≤ (4 * ‖f - g‖ * inverseBound c M) * inverseBound c M :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (norm_inverseOfNormLower_le_uniform f hc hf hfM) hA)
        (norm_inverseOfNormLower_le_uniform g hc hg hgM) (norm_nonneg _) (mul_nonneg hA hB)
    _ = _ := by ring

/-- Actual Hölder functions with the two genuine quantitative bounds. -/
abbrev BoundedNormLowerDomain (γ : ℝ≥0) (c M : ℝ) :=
  {f : HolderFunctionSpace X ℂ γ // ‖f‖ ≤ M ∧ ∀ x, c ≤ ‖f x‖}

def inverseOnBoundedNormLower (γ : ℝ≥0) {c M : ℝ} (hc : 0 < c)
    (f : BoundedNormLowerDomain (X := X) γ c M) : HolderFunctionSpace X ℂ γ :=
  inverseOfNormLower f.val hc f.property.2

def inverseLipschitzConstant (c M : ℝ) : ℝ≥0 := ⟨4 * (inverseBound c M) ^ 2, by positivity⟩

theorem lipschitzWith_inverseOnBoundedNormLower (γ : ℝ≥0) {c M : ℝ} (hc : 0 < c) :
    LipschitzWith (inverseLipschitzConstant c M)
      (inverseOnBoundedNormLower (X := X) γ (M := M) hc) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have ho : dist (inverseOnBoundedNormLower γ hc f) (inverseOnBoundedNormLower γ hc g) =
      ‖inverseOnBoundedNormLower γ hc f - inverseOnBoundedNormLower γ hc g‖ :=
    @dist_eq_norm (HolderFunctionSpace X ℂ γ) inferInstance _ _
  have hi : dist f g = ‖f.val - g.val‖ :=
    @dist_eq_norm (HolderFunctionSpace X ℂ γ) inferInstance f.val g.val
  rw [ho, hi]
  exact norm_sub_inverseOfNormLower_le_uniform f.val g.val hc f.property.2 g.property.2
    f.property.1 g.property.1

theorem continuous_inverseOnBoundedNormLower (γ : ℝ≥0) {c M : ℝ} (hc : 0 < c) :
    Continuous (inverseOnBoundedNormLower (X := X) γ (M := M) hc) :=
  (lipschitzWith_inverseOnBoundedNormLower γ hc).continuous

/-- Actual norm convergence of the reciprocal under a common positive
lower bound.  No global upper norm bound on the approximating family is needed. -/
theorem tendsto_inverseOfNormLower {ι : Type*} {l : Filter ι}
    {u : ι → HolderFunctionSpace X ℂ γ} {f : HolderFunctionSpace X ℂ γ}
    {c : ℝ} (hc : 0 < c) (hu : ∀ i x, c ≤ ‖u i x‖) (hf : ∀ x, c ≤ ‖f x‖)
    (hlim : Tendsto u l (𝓝 f)) :
    Tendsto (fun i => inverseOfNormLower (u i) hc (hu i)) l (𝓝 (inverseOfNormLower f hc hf)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hdist : Tendsto (fun i => ‖u i - f‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hlim
  have hB : Tendsto (fun i => inverseBound c ‖u i‖) l (𝓝 (inverseBound c ‖f‖)) :=
    tendsto_const_nhds.max (hlim.norm.div_const (c ^ 2))
  have hfour : Tendsto (fun _ : ι => (4 : ℝ)) l (𝓝 4) := tendsto_const_nhds
  have hfix : Tendsto (fun _ : ι => ‖inverseOfNormLower f hc hf‖) l
      (𝓝 ‖inverseOfNormLower f hc hf‖) := tendsto_const_nhds
  have hmajor : Tendsto (fun i =>
      4 * ‖u i - f‖ * inverseBound c ‖u i‖ * ‖inverseOfNormLower f hc hf‖) l (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using ((hfour.mul hdist).mul hB).mul hfix
  apply squeeze_zero (fun _ => norm_nonneg _) _ hmajor
  intro i
  apply (norm_sub_inverseOfNormLower_le (u i) f hc (hu i) hf).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_inverseOfNormLower_le (u i) hc (hu i))
      (mul_nonneg (by norm_num) (norm_nonneg _))) (norm_nonneg _)

/-- The literal boundary phase, as an actual Hölder function. -/
def phaseOfNormLower (f : HolderFunctionSpace X ℂ γ) {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) : HolderFunctionSpace X ℂ γ :=
  pointwiseMul (conjugate f) (inverseOfNormLower f hc hf)

@[simp] theorem phaseOfNormLower_apply (f : HolderFunctionSpace X ℂ γ) {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) (x : X) :
    phaseOfNormLower f hc hf x = conj (f x) / f x := by
  rw [div_eq_mul_inv]
  rfl

theorem norm_phaseOfNormLower_apply (f : HolderFunctionSpace X ℂ γ) {c : ℝ}
    (hc : 0 < c) (hf : ∀ x, c ≤ ‖f x‖) (x : X) : ‖phaseOfNormLower f hc hf x‖ = 1 := by
  rw [phaseOfNormLower_apply, norm_div, Complex.norm_conj]
  exact div_self (ne_of_gt (hc.trans_le (hf x)))

def phaseOnBoundedNormLower (γ : ℝ≥0) {c M : ℝ} (hc : 0 < c)
    (f : BoundedNormLowerDomain (X := X) γ c M) : HolderFunctionSpace X ℂ γ :=
  phaseOfNormLower f.val hc f.property.2

theorem continuous_phaseOnBoundedNormLower (γ : ℝ≥0) {c M : ℝ} (hc : 0 < c) :
    Continuous (phaseOnBoundedNormLower (X := X) γ (M := M) hc) := by
  have hconj : Continuous (fun f : BoundedNormLowerDomain (X := X) γ c M => conjugate f.val) :=
    ((conjugateCLM γ).continuous.comp continuous_subtype_val).congr (fun _ => rfl)
  have hi := continuous_inverseOnBoundedNormLower (X := X) γ (M := M) hc
  exact ((pointwiseMulCLM γ).isBoundedBilinearMap.continuous.comp (hconj.prodMk hi)).congr
    (fun _ => rfl)

theorem tendsto_phaseOfNormLower {ι : Type*} {l : Filter ι}
    {u : ι → HolderFunctionSpace X ℂ γ} {f : HolderFunctionSpace X ℂ γ}
    {c : ℝ} (hc : 0 < c) (hu : ∀ i x, c ≤ ‖u i x‖) (hf : ∀ x, c ≤ ‖f x‖)
    (hlim : Tendsto u l (𝓝 f)) :
    Tendsto (fun i => phaseOfNormLower (u i) hc (hu i)) l (𝓝 (phaseOfNormLower f hc hf)) := by
  have hconj : Tendsto (fun i => conjugate (u i)) l (𝓝 (conjugate f)) :=
    (((conjugateCLM γ).continuous.tendsto f).comp hlim).congr' (Eventually.of_forall (fun _ => rfl))
  have hi := tendsto_inverseOfNormLower hc hu hf hlim
  exact (((pointwiseMulCLM γ).isBoundedBilinearMap.continuous.tendsto
    (conjugate f, inverseOfNormLower f hc hf)).comp (hconj.prodMk_nhds hi)).congr'
      (Eventually.of_forall (fun _ => rfl))

end Euler2D.HolderFunctionSpace

end
