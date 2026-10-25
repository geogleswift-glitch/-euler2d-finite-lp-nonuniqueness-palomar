module

public import RequestProject.Euler.Stationary
public import RequestProject.Euler.StationaryLimit
public import RequestProject.Euler.DatumSeries
public import RequestProject.Euler.KernelIdentities
public import RequestProject.Euler.LimitPassage

/-!
# Actual radial velocity blocks

`cellW` and `datumTerm` are scalar vorticities. Their circular velocity
profile is `cellOmega ‖x‖ • perpJ x`. This file works with that vector
field, translating its unit support disk into the interior of the
fundamental square before constructing a torus datum.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

noncomputable section

namespace Euler2D

/-- The circular angular velocity as a continuous function of squared radius.
The minimum and maximum encode the two physical interfaces without a
singularity at the origin. -/
def cellOmegaSq (s : ℝ) : ℝ :=
  3 * (1 - min (max s (3 / 5)) 1) / (4 * max s (3 / 5))

lemma cellOmega_eq_sq (r : ℝ) (hr : 0 ≤ r) : cellOmega r = cellOmegaSq (r ^ 2) := by
  have ha := cellA_pos
  have ha1 := cellA_lt_one
  have ha2 := cellA_sq
  unfold cellOmega cellOmegaSq
  split_ifs with h1 h2
  · have hs : r ^ 2 ≤ (3 / 5 : ℝ) := by nlinarith
    rw [max_eq_right hs, min_eq_left (by norm_num : (3 / 5 : ℝ) ≤ 1)]
    norm_num
  · have hs : (3 / 5 : ℝ) ≤ r ^ 2 := by nlinarith
    have hs1 : r ^ 2 ≤ 1 := by nlinarith
    rw [max_eq_left hs, min_eq_left hs1]
  · have hs1 : (1 : ℝ) ≤ r ^ 2 := by nlinarith
    have hs : (3 / 5 : ℝ) ≤ r ^ 2 := by linarith
    rw [max_eq_left hs, min_eq_right hs1]
    simp

lemma continuous_cellOmegaSq : Continuous cellOmegaSq := by
  unfold cellOmegaSq
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro s
    have h : (0 : ℝ) < max s (3 / 5) := (by norm_num : (0 : ℝ) < 3 / 5).trans_le (le_max_right _ _)
    positivity

/-- The explicit vector velocity of the circular two-interface cell. -/
def cellVelocity (x : R2) : R2 := cellOmega ‖x‖ • perpJ x

lemma cellVelocity_eq_sq (x : R2) :
    cellVelocity x = cellOmegaSq (‖x‖ ^ 2) • perpJ x := by
  rw [cellVelocity, cellOmega_eq_sq _ (norm_nonneg _)]

lemma continuous_cellVelocity : Continuous cellVelocity := by
  simp_rw [show cellVelocity = fun x => cellOmegaSq (‖x‖ ^ 2) • perpJL x from
    funext fun x => cellVelocity_eq_sq x]
  exact (continuous_cellOmegaSq.comp (continuous_norm.pow 2)).smul perpJL.continuous

lemma perpJ_neg (x : R2) : perpJ (-x) = -perpJ x := by
  ext i
  fin_cases i <;> simp [perpJ]

/-- The actual circular velocity is odd. -/
lemma cellVelocity_neg (x : R2) : cellVelocity (-x) = -cellVelocity x := by
  simp [cellVelocity, perpJ_neg]

/-- The circular velocity vanishes outside the unit disk, including its boundary. -/
lemma cellVelocity_eq_zero_of_one_le_norm {x : R2} (hx : 1 ≤ ‖x‖) : cellVelocity x = 0 := by
  rw [cellVelocity, cellOmega_interfaces.2.2.2 _ hx, zero_smul]

lemma support_cellVelocity_subset : Function.support cellVelocity ⊆ Metric.closedBall 0 1 := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  exact hx (cellVelocity_eq_zero_of_one_le_norm (le_of_lt (lt_of_not_ge h)))

lemma hasCompactSupport_cellVelocity : HasCompactSupport cellVelocity := by
  exact (isCompact_closedBall (0 : R2) (1 : ℝ)).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal support_cellVelocity_subset isClosed_closedBall)

lemma cellVelocity_memLp (q : ENNReal) : MemLp cellVelocity q volume :=
  continuous_cellVelocity.memLp_of_hasCompactSupport hasCompactSupport_cellVelocity

/-- The circular velocity has zero planar mean by oddness. -/
lemma integral_cellVelocity : ∫ x, cellVelocity x = 0 := by
  have hneg : (∫ x, cellVelocity x) = -(∫ x, cellVelocity x) := by
    calc
      (∫ x, cellVelocity x) = ∫ x, cellVelocity (-x) := (integral_neg_eq_self cellVelocity volume).symm
      _ = -(∫ x, cellVelocity x) := by simp_rw [cellVelocity_neg, integral_neg]
  ext i
  have hi := congrArg (fun x : R2 => x i) hneg
  have : (∫ x, cellVelocity x) i = 0 := by
    change (∫ x, cellVelocity x) i = -(∫ x, cellVelocity x) i at hi
    linarith
  simpa using this

/-- The center of the actual fundamental square. -/
def torusCenter : R2 := torusVec Real.pi Real.pi

@[simp] lemma torusCenter_apply (i : Fin 2) : torusCenter i = Real.pi := by
  fin_cases i <;> rfl

/-- The circular velocity block placed inside the torus coordinate square. -/
def centeredCellVelocity (x : R2) : R2 := cellVelocity (x - torusCenter)

lemma continuous_centeredCellVelocity : Continuous centeredCellVelocity :=
  continuous_cellVelocity.comp (continuous_id.sub continuous_const)

lemma support_centeredCellVelocity_subset : Function.support centeredCellVelocity ⊆ torusBox := by
  intro x hx i
  have hn : ‖x - torusCenter‖ < 1 := by
    by_contra hn
    exact hx (cellVelocity_eq_zero_of_one_le_norm (le_of_not_gt hn))
  have hc : |x i - Real.pi| < 1 := by
    simpa only [PiLp.sub_apply, torusCenter_apply] using (abs_coord_le (x - torusCenter) i).trans_lt hn
  rw [abs_lt] at hc
  constructor <;> linarith [Real.pi_gt_three]

lemma hasCompactSupport_centeredCellVelocity : HasCompactSupport centeredCellVelocity := by
  apply (isCompact_closedBall torusCenter (1 : ℝ)).of_isClosed_subset
    (isClosed_tsupport centeredCellVelocity)
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  by_contra hn
  exact hx (cellVelocity_eq_zero_of_one_le_norm (le_of_lt (lt_of_not_ge hn)))

lemma centeredCellVelocity_memLp (q : ENNReal) : MemLp centeredCellVelocity q μT :=
  (continuous_centeredCellVelocity.memLp_of_hasCompactSupport
    hasCompactSupport_centeredCellVelocity).mono_measure Measure.restrict_le_self

/-- The physical centered circular block has zero mean on the actual torus domain. -/
lemma integral_centeredCellVelocity : ∫ x in torusBox, centeredCellVelocity x = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact (integral_sub_right_eq_self cellVelocity torusCenter).trans integral_cellVelocity
  · intro x hx
    by_contra hn
    exact hx (support_centeredCellVelocity_subset hn)

/-- The actual centered circular velocity as a torus `L²` datum. -/
def centeredCellVelocityLp : L2T := (centeredCellVelocity_memLp 2).toLp centeredCellVelocity

lemma integral_centeredCellVelocityLp : ∫ x in torusBox, centeredCellVelocityLp x = 0 := by
  rw [← integral_centeredCellVelocity]
  apply integral_congr_ae
  exact (centeredCellVelocity_memLp 2).coeFn_toLp

/-- The physical scaling of a velocity block, distinct from the vorticity scaling. -/
def scaledCellVelocity (A r : ℝ) (x : R2) : R2 := (A * r) • cellVelocity (r⁻¹ • x)

lemma scaledCellVelocity_eq {r : ℝ} (hr : 0 < r) (A : ℝ) (x : R2) :
    scaledCellVelocity A r x = (A * cellOmega (r⁻¹ * ‖x‖)) • perpJ x := by
  unfold scaledCellVelocity cellVelocity
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), perpJ_smul]
  simp only [smul_smul]
  congr 1
  field_simp

/-- Matching opposite coordinate faces suffices for integration over one
fundamental square; no extension of the field outside that square is required. -/
def MatchesTorusFaces {F : Type*} (h : R2 → F) : Prop :=
  ∀ x (i : Fin 2), x i = 0 → h (x + EuclideanSpace.single i (2 * Real.pi)) = h x

lemma IsTorusPeriodic.matchesTorusFaces {F : Type*} {h : R2 → F}
    (hh : IsTorusPeriodic h) : MatchesTorusFaces h := fun x i _ => hh x i

lemma MatchesTorusFaces.mul {f g : R2 → ℝ}
    (hf : MatchesTorusFaces f) (hg : MatchesTorusFaces g) :
    MatchesTorusFaces (fun x => f x * g x) := by
  intro x i hx
  dsimp only
  rw [hf x i hx, hg x i hx]

lemma integral_pd_line_of_matching_faces (h : R2 → ℝ) (hh : ContDiff ℝ 1 h)
    (hp : MatchesTorusFaces h) (i : Fin 2) (x : R2) (hx : x i = 0) :
    ∫ r in (0 : ℝ)..(2 * Real.pi), pd i h (x + r • EuclideanSpace.single i 1) = 0 := by
  have hc : Continuous (fun r : ℝ => pd i h (x + r • EuclideanSpace.single i 1)) :=
    (continuous_pd_of_contDiff_one h hh i).comp (by fun_prop)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hasDerivAt_coordinate_line h x i r (hh.differentiable one_ne_zero _))
    (hc.intervalIntegrable _ _)]
  have hsingle : (2 * Real.pi) • EuclideanSpace.single i (1 : ℝ) =
      EuclideanSpace.single i (2 * Real.pi) := by
    ext j
    simp [EuclideanSpace.single_apply]
  simp only [zero_smul, add_zero]
  rw [hsingle, hp x i hx, sub_self]

lemma integral_pd_eq_zero_of_matching_faces (h : R2 → ℝ) (hh : ContDiff ℝ 1 h)
    (hp : MatchesTorusFaces h) (i : Fin 2) : ∫ x in torusBox, pd i h x = 0 := by
  have hc := continuous_pd_of_contDiff_one h hh i
  fin_cases i
  · rw [integral_torusBox_swap _ hc]
    have hline (b : ℝ) : ∫ a in (0 : ℝ)..(2 * Real.pi), pd 0 h (torusVec a b) = 0 := by
      have heq (a : ℝ) : torusVec a b = torusVec 0 b + a • EuclideanSpace.single 0 1 := by
        ext j
        fin_cases j <;> simp [torusVec, EuclideanSpace.single_apply]
      rw [show (fun a => pd 0 h (torusVec a b)) =
        (fun a => pd 0 h (torusVec 0 b + a • EuclideanSpace.single 0 1)) from
          funext fun a => congrArg (pd 0 h) (heq a)]
      exact integral_pd_line_of_matching_faces h hh hp 0 _ (by simp)
    simp [hline]
  · rw [integral_torusBox _ hc]
    have hline (a : ℝ) : ∫ b in (0 : ℝ)..(2 * Real.pi), pd 1 h (torusVec a b) = 0 := by
      have heq (b : ℝ) : torusVec a b = torusVec a 0 + b • EuclideanSpace.single 1 1 := by
        ext j
        fin_cases j <;> simp [torusVec, EuclideanSpace.single_apply]
      rw [show (fun b => pd 1 h (torusVec a b)) =
        (fun b => pd 1 h (torusVec a 0 + b • EuclideanSpace.single 1 1)) from
          funext fun b => congrArg (pd 1 h) (heq b)]
      exact integral_pd_line_of_matching_faces h hh hp 1 _ (by simp)
    simp [hline]

/-- Integration by parts needs only matching traces at opposite faces. -/
lemma integral_mul_pd_matching_faces (f g : R2 → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfp : MatchesTorusFaces f) (hgp : MatchesTorusFaces g) (i : Fin 2) :
    ∫ x in torusBox, f x * pd i g x = -∫ x in torusBox, pd i f x * g x := by
  have h0 := integral_pd_eq_zero_of_matching_faces _ (hf.mul hg) (hfp.mul hgp) i
  have heq (x : R2) : pd i (fun y => f y * g y) x = pd i f x * g x + f x * pd i g x :=
    torus_pd_mul f g x (hf.differentiable one_ne_zero x) (hg.differentiable one_ne_zero x) i
  simp_rw [heq] at h0
  rw [integral_add (f := fun x => pd i f x * g x) (g := fun x => f x * pd i g x)
    (integrable_torusBox_of_continuous
      ((continuous_pd_of_contDiff_one f hf i).mul hg.continuous))
    (integrable_torusBox_of_continuous
      (hf.continuous.mul (continuous_pd_of_contDiff_one g hg i)))] at h0
  linarith

theorem isStationary_of_convective_gradient_matching_faces {v : L2T} {u : R2 → R2}
    (hvu : (v : R2 → R2) =ᵐ[μT] u) (hu : ContDiff ℝ 1 u)
    (hup : MatchesTorusFaces u) (hdiv : ∀ x, pd 0 u x 0 + pd 1 u x 1 = 0)
    (P : R2 → ℝ) (hP : ContDiff ℝ 1 P) (hPp : MatchesTorusFaces P)
    (hconv : ∀ x i, (∑ j : Fin 2, u x j * pd j u x i) = pd i P x) :
    IsStationary v := by
  intro ψ hψ hψp hψdiv
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
  have huc (i : Fin 2) : ContDiff ℝ 1 (fun x => u x i) :=
    (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).contDiff.comp hu
  have hψc (i : Fin 2) : ContDiff ℝ 1 (fun x => ψ x i) :=
    (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).contDiff.comp hψ1
  have hupc (i : Fin 2) : MatchesTorusFaces (fun x => u x i) := by
    intro x j hx
    exact congrArg (fun y : R2 => y i) (hup x j hx)
  have hψpc (i : Fin 2) : MatchesTorusFaces (fun x => ψ x i) := by
    intro x j hx
    exact congrArg (fun y : R2 => y i) (hψp x j)
  have hupd (x : R2) (i j : Fin 2) : pd j (fun y => u y i) x = pd j u x i :=
    torus_pd_component u x (hu.differentiable one_ne_zero x) j i
  have hψpd (x : R2) (i j : Fin 2) : pd j (fun y => ψ y i) x = pd j ψ x i :=
    torus_pd_component ψ x (hψ1.differentiable one_ne_zero x) j i
  have hprod (x : R2) (i j : Fin 2) :
      pd j (fun y => u y i * u y j) x = pd j u x i * u x j + u x i * pd j u x j := by
    rw [torus_pd_mul _ _ x ((huc i).differentiable one_ne_zero x)
      ((huc j).differentiable one_ne_zero x), hupd, hupd]
  have hflux (x : R2) (i : Fin 2) :
      (∑ j : Fin 2, pd j (fun y => u y i * u y j) x) = pd i P x := by
    simp_rw [hprod]
    have hc := hconv x i
    have hd := hdiv x
    simp only [Fin.sum_univ_two] at hc ⊢
    linear_combination hc + u x i * hd
  have hpair (i j : Fin 2) :
      (∫ x in torusBox, u x i * u x j * pd j ψ x i) =
        -∫ x in torusBox, pd j (fun y => u y i * u y j) x * ψ x i := by
    simpa only [hψpd] using integral_mul_pd_matching_faces (fun x => u x i * u x j)
      (fun x => ψ x i) ((huc i).mul (huc j)) (hψc i) ((hupc i).mul (hupc j)) (hψpc i) j
  have hI (i j : Fin 2) : Integrable (fun x => u x i * u x j * pd j ψ x i) μT := by
    apply integrable_torusBox_of_continuous
    exact ((huc i).continuous.mul (huc j).continuous).mul
      ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp
        (continuous_pd_of_contDiff_one ψ hψ1 j))
  have hJ (i j : Fin 2) :
      Integrable (fun x => pd j (fun y => u y i * u y j) x * ψ x i) μT :=
    integrable_torusBox_of_continuous
      ((continuous_pd_of_contDiff_one _ ((huc i).mul (huc j)) j).mul (hψc i).continuous)
  have hK (i : Fin 2) : Integrable (fun x => P x * pd i ψ x i) μT :=
    integrable_torusBox_of_continuous (hP.continuous.mul
      ((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp
        (continuous_pd_of_contDiff_one ψ hψ1 i)))
  have hae : (fun x => ∑ i, ∑ j, v x i * v x j * pd j ψ x i) =ᵐ[μT]
      (fun x => ∑ i, ∑ j, u x i * u x j * pd j ψ x i) := by
    filter_upwards [hvu] with x hx
    rw [hx]
  rw [integral_congr_ae hae]
  calc
    (∫ x in torusBox, ∑ i, ∑ j, u x i * u x j * pd j ψ x i) =
        ∑ i, ∑ j, ∫ x in torusBox, u x i * u x j * pd j ψ x i := by
      rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hI i j))]
      exact Finset.sum_congr rfl fun i _ => integral_finset_sum _ (fun j _ => hI i j)
    _ = ∑ i, -∫ x in torusBox, (∑ j : Fin 2, pd j (fun y => u y i * u y j) x) * ψ x i := by
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [hpair]
      rw [Finset.sum_neg_distrib]
      congr 1
      simp_rw [Finset.sum_mul]
      exact (integral_finset_sum _ (fun j _ => hJ i j)).symm
    _ = ∑ i, -∫ x in torusBox, pd i P x * ψ x i := by simp_rw [hflux]
    _ = ∑ i, ∫ x in torusBox, P x * pd i ψ x i := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      simpa only [hψpd] using integral_mul_pd_matching_faces P (fun x => ψ x i)
        hP (hψc i) hPp (hψpc i) i
    _ = ∫ x in torusBox, P x * (∑ i : Fin 2, pd i ψ x i) := by
      simp_rw [Finset.mul_sum]
      exact (integral_finset_sum _ (fun i _ => hK i)).symm
    _ = 0 := by
      have hz (x : R2) : (∑ i : Fin 2, pd i ψ x i) = 0 := by
        simpa only [Fin.sum_univ_two] using hψdiv x
      simp_rw [hz, mul_zero]
      simp


/-- A radial rotating velocity, parameterized by squared radius. -/
def radialVelocity (f : ℝ → ℝ) (c : R2) (x : R2) : R2 :=
  f (‖x - c‖ ^ 2) • perpJ (x - c)

lemma contDiff_radialVelocity {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (c : R2) :
    ContDiff ℝ 1 (radialVelocity f c) := by
  exact (hf.comp ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ))).smul
    (perpJL.contDiff.comp (contDiff_id.sub contDiff_const))

lemma fderiv_radialVelocity_apply {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (c x v : R2) :
    fderiv ℝ (radialVelocity f c) x v =
      (2 * deriv f (‖x - c‖ ^ 2) * inner ℝ (x - c) v) • perpJ (x - c) +
        f (‖x - c‖ ^ 2) • perpJ v := by
  have hz : HasFDerivAt (fun y : R2 => y - c) (ContinuousLinearMap.id ℝ R2) x :=
    (hasFDerivAt_id (𝕜 := ℝ) x).sub_const c
  have hs := (hf (‖x - c‖ ^ 2)).hasDerivAt.comp_hasFDerivAt x hz.norm_sq
  have hJ := perpJL.hasFDerivAt.comp x hz
  have hd := hs.smul hJ
  have hdf := hd.fderiv
  change fderiv ℝ (radialVelocity f c) x = _ at hdf
  rw [hdf]
  ext i
  simp [ContinuousLinearMap.smulRight_apply, inner_sub_left]
  ring

lemma radialVelocity_divergence {f : ℝ → ℝ} (hf : Differentiable ℝ f) (c x : R2) :
    pd 0 (radialVelocity f c) x 0 + pd 1 (radialVelocity f c) x 1 = 0 := by
  unfold pd
  rw [fderiv_radialVelocity_apply hf, fderiv_radialVelocity_apply hf]
  simp [EuclideanSpace.inner_single_right, perpJ, EuclideanSpace.single_apply]
  ring

lemma radialVelocity_convective {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (c x : R2) (i : Fin 2) :
    (∑ j : Fin 2, radialVelocity f c x j * pd j (radialVelocity f c) x i) =
      -(f (‖x - c‖ ^ 2) ^ 2) * (x - c) i := by
  simp only [Fin.sum_univ_two, pd, fderiv_radialVelocity_apply hf]
  fin_cases i <;>
    simp [radialVelocity, EuclideanSpace.inner_single_right, perpJ,
      EuclideanSpace.single_apply] <;> ring

/-- The radial antiderivative generating the pressure. -/
def radialPrimitive (f : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, f t ^ 2

lemma hasDerivAt_radialPrimitive {f : ℝ → ℝ} (hf : Continuous f) (s : ℝ) :
    HasDerivAt (radialPrimitive f) (f s ^ 2) s :=
  intervalIntegral.integral_hasDerivAt_right ((hf.pow 2).intervalIntegrable _ _)
    (hf.pow 2).aestronglyMeasurable.stronglyMeasurableAtFilter (hf.pow 2).continuousAt

lemma contDiff_radialPrimitive {f : ℝ → ℝ} (hf : Continuous f) :
    ContDiff ℝ 1 (radialPrimitive f) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun s => (hasDerivAt_radialPrimitive hf s).differentiableAt, ?_⟩
  have heq : deriv (radialPrimitive f) = fun s => f s ^ 2 :=
    funext fun s => (hasDerivAt_radialPrimitive hf s).deriv
  rw [heq]
  exact hf.pow 2

/-- A concrete pressure potential for a radial rotating velocity. -/
def radialPressure (f : ℝ → ℝ) (c : R2) (x : R2) : ℝ :=
  (-1 / 2 : ℝ) * radialPrimitive f (‖x - c‖ ^ 2)

lemma contDiff_radialPressure {f : ℝ → ℝ} (hf : Continuous f) (c : R2) :
    ContDiff ℝ 1 (radialPressure f c) :=
  contDiff_const.mul ((contDiff_radialPrimitive hf).comp
    ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ)))

lemma pd_radialPressure {f : ℝ → ℝ} (hf : Continuous f) (c x : R2) (i : Fin 2) :
    pd i (radialPressure f c) x = -(f (‖x - c‖ ^ 2) ^ 2) * (x - c) i := by
  have hz : HasFDerivAt (fun y : R2 => y - c) (ContinuousLinearMap.id ℝ R2) x :=
    (hasFDerivAt_id (𝕜 := ℝ) x).sub_const c
  have hp := ((hasDerivAt_radialPrimitive hf (‖x - c‖ ^ 2)).comp_hasFDerivAt x
    hz.norm_sq).const_mul (-1 / 2 : ℝ)
  have hpf := hp.fderiv
  change fderiv ℝ (radialPressure f c) x = _ at hpf
  unfold pd
  rw [hpf]
  simp [EuclideanSpace.inner_single_right]
  ring

/-- Reflection from one face to its opposite preserves squared distance
from the center of the fundamental square. -/
lemma norm_sq_sub_center_face (x : R2) (i : Fin 2) (hx : x i = 0) :
    ‖x + EuclideanSpace.single i (2 * Real.pi) - torusCenter‖ ^ 2 =
      ‖x - torusCenter‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  fin_cases i
  · change x 0 = 0 at hx
    simp [EuclideanSpace.single_apply, hx]
    ring
  · change x 1 = 0 at hx
    simp [EuclideanSpace.single_apply, hx]
    ring

lemma radialPressure_matchesTorusFaces (f : ℝ → ℝ) :
    MatchesTorusFaces (radialPressure f torusCenter) := by
  intro x i hx
  unfold radialPressure
  rw [norm_sq_sub_center_face x i hx]

lemma one_le_norm_sq_sub_center_of_face (x : R2) (i : Fin 2)
    (hx : x i = 0 ∨ x i = 2 * Real.pi) : 1 ≤ ‖x - torusCenter‖ ^ 2 := by
  have hcoord : |x i - Real.pi| ≤ ‖x - torusCenter‖ := by
    simpa only [PiLp.sub_apply, torusCenter_apply] using abs_coord_le (x - torusCenter) i
  have hn : Real.pi ≤ ‖x - torusCenter‖ := by
    rcases hx with hx | hx
    · rw [hx, zero_sub, abs_neg, abs_of_pos Real.pi_pos] at hcoord
      exact hcoord
    · rw [hx, show 2 * Real.pi - Real.pi = Real.pi by ring, abs_of_pos Real.pi_pos] at hcoord
      exact hcoord
  nlinarith [Real.pi_gt_three]

lemma radialVelocity_matchesTorusFaces {f : ℝ → ℝ}
    (hzero : ∀ s, 1 ≤ s → f s = 0) : MatchesTorusFaces (radialVelocity f torusCenter) := by
  intro x i hx
  have hy : (x + EuclideanSpace.single i (2 * Real.pi)) i = 2 * Real.pi := by
    simp [hx, EuclideanSpace.single_apply]
  simp only [radialVelocity,
    hzero _ (one_le_norm_sq_sub_center_of_face _ i (Or.inl hx)),
    hzero _ (one_le_norm_sq_sub_center_of_face _ i (Or.inr hy)), zero_smul]

/-- Every `C¹` radial profile vanishing outside the unit disk produces a
stationary torus datum. The pressure is explicitly constructed, rather
than being supplied as an Euler-equation assumption. -/
theorem isStationary_radialVelocity {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hzero : ∀ s, 1 ≤ s → f s = 0) {v : L2T}
    (hveq : (v : R2 → R2) =ᵐ[μT] radialVelocity f torusCenter) : IsStationary v := by
  apply isStationary_of_convective_gradient_matching_faces hveq
    (contDiff_radialVelocity hf torusCenter) (radialVelocity_matchesTorusFaces hzero)
    (radialVelocity_divergence (hf.differentiable one_ne_zero) torusCenter)
    (radialPressure f torusCenter) (contDiff_radialPressure hf.continuous torusCenter)
    (radialPressure_matchesTorusFaces f)
  intro x i
  rw [radialVelocity_convective (hf.differentiable one_ne_zero), pd_radialPressure hf.continuous]

/-- A scalar primitive used to smooth a continuous radial profile. -/
def profilePrimitive (f : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, f t

lemma hasDerivAt_profilePrimitive {f : ℝ → ℝ} (hf : Continuous f) (s : ℝ) :
    HasDerivAt (profilePrimitive f) (f s) s :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

lemma contDiff_profilePrimitive {f : ℝ → ℝ} (hf : Continuous f) :
    ContDiff ℝ 1 (profilePrimitive f) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun s => (hasDerivAt_profilePrimitive hf s).differentiableAt, ?_⟩
  have heq : deriv (profilePrimitive f) = f :=
    funext fun s => (hasDerivAt_profilePrimitive hf s).deriv
  rwa [heq]

/-- The forward average of a profile. Forward averaging preserves the
exact exterior cutoff `f s = 0` for `s ≥ 1`. -/
def profileAverage (f : ℝ → ℝ) (ε s : ℝ) : ℝ :=
  ε⁻¹ * (profilePrimitive f (s + ε) - profilePrimitive f s)

lemma contDiff_profileAverage {f : ℝ → ℝ} (hf : Continuous f) (ε : ℝ) :
    ContDiff ℝ 1 (profileAverage f ε) :=
  contDiff_const.mul (((contDiff_profilePrimitive hf).comp
    (contDiff_id.add contDiff_const)).sub (contDiff_profilePrimitive hf))

lemma profileAverage_eq_integral {f : ℝ → ℝ} (hf : Continuous f) (ε s : ℝ) :
    profileAverage f ε s = ε⁻¹ * ∫ t in s..(s + ε), f t := by
  unfold profileAverage profilePrimitive
  congr 1
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable (μ := volume) 0 s) (hf.intervalIntegrable (μ := volume) s (s + ε))
  linarith

lemma profileAverage_eq_zero {f : ℝ → ℝ} (hf : Continuous f)
    (hzero : ∀ s, 1 ≤ s → f s = 0) {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : 1 ≤ s) :
    profileAverage f ε s = 0 := by
  rw [profileAverage_eq_integral hf, intervalIntegral.integral_of_le (by linarith)]
  have hz : (∫ t in Ioc s (s + ε), f t) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun t ht => hzero t (hs.trans ht.1.le)
  rw [hz, mul_zero]

lemma norm_profileAverage_le {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hbound : ∀ s, 0 ≤ s → ‖f s‖ ≤ C) {ε : ℝ} (hε : 0 < ε)
    {s : ℝ} (hs : 0 ≤ s) : ‖profileAverage f ε s‖ ≤ C := by
  rw [profileAverage_eq_integral hf, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
  have hb : ‖∫ t in s..(s + ε), f t‖ ≤ C * ε := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := s) (b := s + ε) (C := C) (f := f) (fun t ht => ?_)
    · simpa only [show s + ε - s = ε by ring, abs_of_pos hε] using h
    · have ht' : t ∈ Ioc s (s + ε) := by
        simpa only [uIoc_of_le (show s ≤ s + ε by linarith)] using ht
      exact hbound t (hs.trans ht'.1.le)
  calc
    ε⁻¹ * ‖∫ t in s..(s + ε), f t‖ ≤ ε⁻¹ * (C * ε) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hε.le)
    _ = C := by field_simp

def radialApproxScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

lemma radialApproxScale_pos (n : ℕ) : 0 < radialApproxScale n := by
  unfold radialApproxScale
  positivity

lemma tendsto_radialApproxScale : Tendsto radialApproxScale atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall radialApproxScale_pos⟩

lemma tendsto_profileAverage {f : ℝ → ℝ} (hf : Continuous f) (s : ℝ) :
    Tendsto (fun n => profileAverage f (radialApproxScale n) s) atTop (𝓝 (f s)) := by
  simpa only [profileAverage, smul_eq_mul, Function.comp_def] using
    (hasDerivAt_profilePrimitive hf s).tendsto_slope_zero_right.comp tendsto_radialApproxScale

lemma continuous_radialVelocity {f : ℝ → ℝ} (hf : Continuous f) (c : R2) :
    Continuous (radialVelocity f c) :=
  (hf.comp ((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2)).smul
    (perpJL.continuous.comp (continuous_id.sub continuous_const))

lemma continuous_vector_memLp_torus {F : Type*} [NormedAddCommGroup F]
    {u : R2 → F} (hu : Continuous u) (q : ENNReal) : MemLp u q μT := by
  obtain ⟨C, hC⟩ := isCompact_closedBox.exists_bound_of_continuousOn hu.continuousOn
  apply MemLp.of_bound hu.aestronglyMeasurable C
  rw [ae_restrict_iff' measurableSet_torusBox]
  exact Eventually.of_forall fun x hx => hC x (torusBox_subset_closedBox hx)

lemma norm_perpJ (x : R2) : ‖perpJ x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [EuclideanSpace.norm_sq_eq, perpJ, Fin.sum_univ_two, add_comm]

/-- The smooth forward-averaged radial field represented in the actual
torus Hilbert space. -/
def radialApproxLp (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ) : L2T :=
  (continuous_vector_memLp_torus
    (continuous_radialVelocity (contDiff_profileAverage hf (radialApproxScale n)).continuous torusCenter)
      2).toLp (radialVelocity (profileAverage f (radialApproxScale n)) torusCenter)

lemma radialApproxLp_ae (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ) :
    (radialApproxLp f hf n : R2 → R2) =ᵐ[μT]
      radialVelocity (profileAverage f (radialApproxScale n)) torusCenter :=
  (continuous_vector_memLp_torus
    (continuous_radialVelocity (contDiff_profileAverage hf (radialApproxScale n)).continuous torusCenter)
      2).coeFn_toLp

lemma isStationary_radialApproxLp {f : ℝ → ℝ} (hf : Continuous f)
    (hzero : ∀ s, 1 ≤ s → f s = 0) (n : ℕ) : IsStationary (radialApproxLp f hf n) :=
  isStationary_radialVelocity (contDiff_profileAverage hf (radialApproxScale n))
    (fun _s hs => profileAverage_eq_zero hf hzero (radialApproxScale_pos n) hs)
    (radialApproxLp_ae f hf n)

/-- Averaging the scalar radial profile converges strongly in the torus
`L²` space. No spatial derivative of the original profile is assumed. -/
lemma tendsto_radialApproxLp {f : ℝ → ℝ} (hf : Continuous f)
    (hzero : ∀ s, 1 ≤ s → f s = 0) {v : L2T}
    (hveq : (v : R2 → R2) =ᵐ[μT] radialVelocity f torusCenter) :
    Tendsto (radialApproxLp f hf) atTop (𝓝 v) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuousOn : ContinuousOn f (Icc (0 : ℝ) 1))
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0 (by constructor <;> norm_num))
  have hbound (s : ℝ) (hs : 0 ≤ s) : ‖f s‖ ≤ C := by
    by_cases hs1 : s ≤ 1
    · exact hC s ⟨hs, hs1⟩
    · rw [hzero s (le_of_lt (lt_of_not_ge hs1)), norm_zero]
      exact hC0
  let F : ℕ → R2 → ℝ := fun n x =>
    ‖radialVelocity (profileAverage f (radialApproxScale n)) torusCenter x -
      radialVelocity f torusCenter x‖ ^ 2
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) μT :=
    ((((continuous_radialVelocity
      (contDiff_profileAverage hf (radialApproxScale n)).continuous torusCenter).sub
        (continuous_radialVelocity hf torusCenter)).norm).pow 2).aestronglyMeasurable
  have hdom (n : ℕ) (x : R2) : ‖F n x‖ ≤ (2 * C) ^ 2 * ‖x - torusCenter‖ ^ 2 := by
    have hs : 0 ≤ ‖x - torusCenter‖ ^ 2 := sq_nonneg _
    have havg := norm_profileAverage_le hf hbound (radialApproxScale_pos n) hs
    have hval := hbound _ hs
    have hscalar : ‖profileAverage f (radialApproxScale n) (‖x - torusCenter‖ ^ 2) -
        f (‖x - torusCenter‖ ^ 2)‖ ≤ 2 * C := by
      exact (norm_sub_le _ _).trans (by linarith)
    have hnorm : ‖radialVelocity (profileAverage f (radialApproxScale n)) torusCenter x -
        radialVelocity f torusCenter x‖ ≤ (2 * C) * ‖x - torusCenter‖ := by
      unfold radialVelocity
      rw [← sub_smul, norm_smul, norm_perpJ]
      exact mul_le_mul_of_nonneg_right hscalar (norm_nonneg _)
    change ‖‖_‖ ^ 2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc
      ‖radialVelocity (profileAverage f (radialApproxScale n)) torusCenter x -
          radialVelocity f torusCenter x‖ ^ 2 ≤ ((2 * C) * ‖x - torusCenter‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))).mpr hnorm
      _ = (2 * C) ^ 2 * ‖x - torusCenter‖ ^ 2 := mul_pow _ _ _
  have hpoint (x : R2) : Tendsto (fun n => F n x) atTop (𝓝 0) := by
    have hvel : Tendsto (fun n => radialVelocity (profileAverage f (radialApproxScale n))
        torusCenter x) atTop (𝓝 (radialVelocity f torusCenter x)) :=
      (tendsto_profileAverage hf (‖x - torusCenter‖ ^ 2)).smul_const (perpJ (x - torusCenter))
    simpa only [F, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((hvel.sub_const (radialVelocity f torusCenter x)).norm).pow 2
  have hint := tendsto_integral_of_dominated_convergence (μ := μT)
    (F := F) (f := fun _ => (0 : ℝ)) (fun x => (2 * C) ^ 2 * ‖x - torusCenter‖ ^ 2)
    hmeas
    ((integrable_torusBox_of_continuous
      ((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2)).const_mul _)
    (fun n => Eventually.of_forall (hdom n)) (Eventually.of_forall hpoint)
  have hsq (n : ℕ) : ‖radialApproxLp f hf n - v‖ ^ 2 = ∫ x, F n x ∂μT := by
    rw [← l2_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (radialApproxLp f hf n) v,
      radialApproxLp_ae f hf n, hveq] with x hsub ha hv
    rw [hsub, Pi.sub_apply, ha, hv]
  have hn2 : Tendsto (fun n => ‖radialApproxLp f hf n - v‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hsq, integral_zero] using hint
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hn := hn2.sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hn

/-- Every continuous compactly supported radial rotating profile is an
actual stationary torus datum, including profiles with circular interfaces. -/
theorem isStationary_of_continuous_radialProfile {f : ℝ → ℝ} (hf : Continuous f)
    (hzero : ∀ s, 1 ≤ s → f s = 0) {v : L2T}
    (hveq : (v : R2 → R2) =ᵐ[μT] radialVelocity f torusCenter) : IsStationary v :=
  IsStationary.of_tendsto (Eventually.of_forall (isStationary_radialApproxLp hf hzero))
    (tendsto_radialApproxLp hf hzero hveq)

theorem divFree_of_pointwise_divergence_zero_matching_faces {v : L2T} {u : R2 → R2}
    (hvu : (v : R2 → R2) =ᵐ[μT] u) (hu : ContDiff ℝ 1 u)
    (hup : MatchesTorusFaces u) (hdiv : ∀ x, pd 0 u x 0 + pd 1 u x 1 = 0) :
    DivFree v := by
  intro ψ hψ
  have hψ1 : ContDiff ℝ 1 ψ := hψ.1.of_le (by exact_mod_cast le_top)
  have huc (i : Fin 2) : ContDiff ℝ 1 (fun x => u x i) :=
    (EuclideanSpace.proj i : R2 →L[ℝ] ℝ).contDiff.comp hu
  have hupc (i : Fin 2) : MatchesTorusFaces (fun x => u x i) := by
    intro x j hx
    exact congrArg (fun y : R2 => y i) (hup x j hx)
  have hupd (x : R2) (i : Fin 2) : pd i (fun y => u y i) x = pd i u x i :=
    torus_pd_component u x (hu.differentiable one_ne_zero x) i i
  have hpair (i : Fin 2) : (∫ x in torusBox, u x i * pd i ψ x) =
      -∫ x in torusBox, pd i u x i * ψ x := by
    simpa only [hupd] using
      integral_mul_pd_matching_faces (fun x => u x i) ψ (huc i) hψ1 (hupc i) hψ.2.matchesTorusFaces i
  have hI (i : Fin 2) : Integrable (fun x => u x i * pd i ψ x) μT :=
    integrable_torusBox_of_continuous
      ((huc i).continuous.mul (continuous_pd_of_contDiff_one ψ hψ1 i))
  have hJ (i : Fin 2) : Integrable (fun x => pd i u x i * ψ x) μT :=
    integrable_torusBox_of_continuous
      (((EuclideanSpace.proj i : R2 →L[ℝ] ℝ).continuous.comp
        (continuous_pd_of_contDiff_one u hu i)).mul hψ1.continuous)
  have hae : (fun x => ∑ i, v x i * pd i ψ x) =ᵐ[μT]
      (fun x => ∑ i, u x i * pd i ψ x) := by
    filter_upwards [hvu] with x hx
    rw [hx]
  rw [integral_congr_ae hae]
  calc
    (∫ x in torusBox, ∑ i, u x i * pd i ψ x) =
        ∑ i, ∫ x in torusBox, u x i * pd i ψ x :=
      integral_finset_sum _ (fun i _ => hI i)
    _ = -∫ x in torusBox, (∑ i : Fin 2, pd i u x i) * ψ x := by
      simp_rw [hpair]
      rw [Finset.sum_neg_distrib]
      congr 1
      simp_rw [Finset.sum_mul]
      exact (integral_finset_sum _ (fun i _ => hJ i)).symm
    _ = 0 := by
      have hz (x : R2) : (∑ i : Fin 2, pd i u x i) = 0 := by
        simpa only [Fin.sum_univ_two] using hdiv x
      simp_rw [hz, zero_mul]
      simp


lemma divFree_radialApproxLp {f : ℝ → ℝ} (hf : Continuous f)
    (hzero : ∀ s, 1 ≤ s → f s = 0) (n : ℕ) : DivFree (radialApproxLp f hf n) :=
  divFree_of_pointwise_divergence_zero_matching_faces (radialApproxLp_ae f hf n)
    (contDiff_radialVelocity (contDiff_profileAverage hf (radialApproxScale n)) torusCenter)
    (radialVelocity_matchesTorusFaces
      (fun _s hs => profileAverage_eq_zero hf hzero (radialApproxScale_pos n) hs))
    (radialVelocity_divergence
      ((contDiff_profileAverage hf (radialApproxScale n)).differentiable one_ne_zero) torusCenter)

/-- A continuous radial rotating profile with compact support is
distributionally divergence free on the actual torus domain. -/
theorem divFree_of_continuous_radialProfile {f : ℝ → ℝ} (hf : Continuous f)
    (hzero : ∀ s, 1 ≤ s → f s = 0) {v : L2T}
    (hveq : (v : R2 → R2) =ᵐ[μT] radialVelocity f torusCenter) : DivFree v :=
  divFree_of_tendsto (tendsto_radialApproxLp hf hzero hveq)
    (Eventually.of_forall (divFree_radialApproxLp hf hzero))

lemma cellOmegaSq_eq_zero_of_one_le (s : ℝ) (hs : 1 ≤ s) : cellOmegaSq s = 0 := by
  unfold cellOmegaSq
  rw [max_eq_left (show (3 / 5 : ℝ) ≤ s by linarith), min_eq_right hs]
  simp

lemma centeredCellVelocityLp_ae_radial :
    (centeredCellVelocityLp : R2 → R2) =ᵐ[μT] radialVelocity cellOmegaSq torusCenter := by
  filter_upwards [(centeredCellVelocity_memLp 2).coeFn_toLp] with x hx
  exact hx.trans (cellVelocity_eq_sq (x - torusCenter))

/-- The actual two-interface circular velocity, placed in the coordinate
disk, is stationary even though its first derivative jumps at the interfaces. -/
theorem isStationary_centeredCellVelocityLp : IsStationary centeredCellVelocityLp :=
  isStationary_of_continuous_radialProfile continuous_cellOmegaSq
    cellOmegaSq_eq_zero_of_one_le centeredCellVelocityLp_ae_radial

/-- The same actual circular velocity satisfies the original weak
incompressibility condition. -/
theorem divFree_centeredCellVelocityLp : DivFree centeredCellVelocityLp :=
  divFree_of_continuous_radialProfile continuous_cellOmegaSq
    cellOmegaSq_eq_zero_of_one_le centeredCellVelocityLp_ae_radial

end Euler2D

end



