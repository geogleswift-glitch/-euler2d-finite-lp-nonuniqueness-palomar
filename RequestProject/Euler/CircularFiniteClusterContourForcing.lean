module

public import RequestProject.Euler.CircularFiniteClusterInvariants
public import RequestProject.Euler.CircularPhysicalContourLittle
public import RequestProject.Euler.TorusPhysicalSourceContinuity

/-! The actual finite inner cluster, transported by one and the same
torus Euler particle system, has a genuine exterior field in the original
little contour space.  Relative cluster confinement is retained as an
explicit geometric hypothesis; the mass, cancellation and forcing norm
are proved from the transported labels. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex ComplexConjugate Set MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D

theorem integral_abs_boxedComplexDensity (w : R2 → ℝ) :
    (∫ z : ℂ, |boxedComplexDensity w z|) = ∫ x in torusBox, |w x| := by
  have he : (fun z => |boxedComplexDensity w z|) =
      boxedComplexDensity (fun x => |w x|) := by
    funext z
    simp only [boxedComplexDensity]
    by_cases hz : complexTorusPoint z ∈ torusBox <;> simp [hz]
  rw [he, integral_boxedComplexDensity]

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def finiteInnerClusterComplexSource (s A₀ b R ρ : ℝ) (N k : ℕ)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) : ℂ → ℝ :=
  boxedComplexDensity (P.finiteInnerClusterSource s A₀ b R ρ N k S t)

def finiteInnerClusterMassBudget (A₀ b R ρ : ℝ) (k : ℕ) : ℝ :=
  finiteLabelMassBound * ampScale A₀ b k * radScale R ρ k ^ 2 *
    (ρ ^ 2 / b) / (1 - ρ ^ 2 / b)

theorem integrable_finiteInnerClusterComplexSource {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N k : ℕ)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) :
    Integrable (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) :=
  integrable_boxedComplexDensity
    (P.integrable_finiteInnerClusterSource hs hA hb hR hRmax hρ hρ1 N k S t)

theorem integral_finiteInnerClusterComplexSource_zero {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N k : ℕ)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ) :
    (∫ z : ℂ, P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t z) = 0 := by
  rw [finiteInnerClusterComplexSource, integral_boxedComplexDensity]
  exact P.integral_finiteInnerClusterSource_zero hs hA hb hR hRmax hρ hρ1 N k S t

theorem finiteInnerClusterComplexSource_fourfold {s A₀ b R ρ a : ℝ} (hs : s ≤ 0)
    (N k : ℕ) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (hS : IsFourfoldBoundedEulerParticleSystem S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (ha1 : a < 1)
    (hsupp : ∀ x ∈ torusBox, a < ‖x - torusCenter‖ →
      P.finiteInnerClusterSource s A₀ b R ρ N k S t x = 0) :
    ∀ z, P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t (I * z) =
      P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t z :=
  boxedComplexDensity_fourfold ha1 hsupp (P.finiteInnerClusterSource_quarterTurn hs N k S hS ht)

theorem finiteInnerClusterComplexSource_fourthAbsoluteMoment_le
    {s A₀ b R ρ a : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hsmall : ρ ^ 2 < b) (N k : ℕ)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t : ℝ)
    (hsupp : ∀ x ∈ torusBox, a < ‖x - torusCenter‖ →
      P.finiteInnerClusterSource s A₀ b R ρ N k S t x = 0) :
    (∫ z : ℂ, ‖z‖ ^ 4 * |P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t z|) ≤
      a ^ 4 * finiteInnerClusterMassBudget A₀ b R ρ k := by
  have hm : (∫ z : ℂ, |P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t z|) ≤
      finiteInnerClusterMassBudget A₀ b R ρ k := by
    rw [finiteInnerClusterComplexSource, integral_abs_boxedComplexDensity]
    exact P.integral_abs_finiteInnerClusterSource_le hs hA hb hR hRmax hρ hρ1 hsmall N k S t
  exact (fourth_le_mass
    (P.integrable_finiteInnerClusterComplexSource hs hA hb hR hRmax hρ hρ1 N k S t)
    (boxedComplexDensity_support hsupp)).trans
      (mul_le_mul_of_nonneg_left hm (by positivity))

/-- The whole actual transported inner cluster generates an original
little-space contour forcing, with its real fourth-moment mass budget.
Only relative support and target separation remain geometric inputs. -/
theorem exists_finiteInnerCluster_contourLittle {η : ℝ≥0} (hη : (η : ℝ) ≤ 1)
    {s A₀ b R ρ a d : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hsmall : ρ ^ 2 < b)
    (N k : ℕ) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (hS : IsFourfoldBoundedEulerParticleSystem S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (ha : 0 ≤ a) (ha1 : a < 1)
    (hsupp : ∀ x ∈ torusBox, a < ‖x - torusCenter‖ →
      P.finiteInnerClusterSource s A₀ b R ρ N k S t x = 0)
    (hd : 0 < d) (hsep : 8 * a ≤ d)
    (Z : LittleContourSpace η) (hZ : ∀ x, d ≤ ‖ContourC1Space.toBCF η Z.val x‖) :
    ∃ Q : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Q θ =
        velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t)
          (LittleContourSpace.lift η Z θ)) ∧
      ‖Q‖ ≤ cauchyContourNormBudget 5 (η : ℝ)
        (a ^ 4 * finiteInnerClusterMassBudget A₀ b R ρ k) d ‖Z‖ := by
  have hi := P.integrable_finiteInnerClusterComplexSource hs hA hb hR hRmax hρ hρ1 N k S t
  have hm := P.integral_finiteInnerClusterComplexSource_zero hs hA hb hR hRmax hρ hρ1 N k S t
  have hy := P.finiteInnerClusterComplexSource_fourfold hs N k S hS ht ha1 hsupp
  have hM := P.finiteInnerClusterComplexSource_fourthAbsoluteMoment_le hs hA hb hR hRmax
    hρ hρ1 hsmall N k S t hsupp
  have hsu := boxedComplexDensity_support hsupp
  obtain ⟨Q, hQ, hn⟩ := exists_clusterContourFieldC1 hη ha hi hsu hm hy hM hd
    (by linarith) Z.val hZ
  have hmem := clusterContourFieldC1_mem_little hη ha hi hsu hm hy hM hd hsep Z hZ Q hQ
  exact ⟨⟨Q, hmem⟩, hQ, hn⟩

/-- At the k-th physical scale the true finite inner-cluster forcing
has the sixth-power ratio once the bootstrap radius is supplied. -/
theorem exists_finiteInnerCluster_contourLittle_rhoSix {η : ℝ≥0} (hη : (η : ℝ) ≤ 1)
    {s A₀ b R ρ c D d L : ℝ} (hs : s ≤ 0)
    (hA : 0 < A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hsmall : ρ ^ 2 < b)
    (N k : ℕ) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (hS : IsFourfoldBoundedEulerParticleSystem S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hc : 0 ≤ c) (hD : 0 ≤ D)
    (ha1 : c * ρ * radScale R ρ k * (1 + D) < 1)
    (hsupp : ∀ x ∈ torusBox, c * ρ * radScale R ρ k * (1 + D) < ‖x - torusCenter‖ →
      P.finiteInnerClusterSource s A₀ b R ρ N k S t x = 0)
    (hd : 0 < d) (hsep : 8 * (c * ρ * (1 + D)) ≤ d)
    (Z : LittleContourSpace η)
    (hZ : ∀ x, d * radScale R ρ k ≤ ‖ContourC1Space.toBCF η Z.val x‖)
    (hL : ‖Z‖ ≤ radScale R ρ k * L) :
    ∃ Q : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Q θ =
        velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t)
          (LittleContourSpace.lift η Z θ)) ∧
      ‖Q‖ / (ampScale A₀ b k * radScale R ρ k) ≤
        (finiteLabelMassBound * cauchyContourNormBudget 5 (η : ℝ) 1 d L) *
          c ^ 4 * ρ ^ 6 * (1 + D) ^ 4 / (b * (1 - ρ ^ 2 / b)) := by
  have hr : 0 < radScale R ρ k := radScale_pos hR hρ k
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have ha : 0 ≤ c * ρ * radScale R ρ k * (1 + D) := by positivity
  have hsepr : 8 * (c * ρ * radScale R ρ k * (1 + D)) ≤ d * radScale R ρ k := by
    nlinarith [mul_le_mul_of_nonneg_right hsep hr.le]
  obtain ⟨Q, hQ, hn⟩ := P.exists_finiteInnerCluster_contourLittle hη hs hA.le hb hR hRmax
    hρ hρ1 hsmall N k S hS ht ha ha1 hsupp (mul_pos hd hr) hsepr Z hZ
  let M := (c * ρ * radScale R ρ k * (1 + D)) ^ 4 *
    finiteInnerClusterMassBudget A₀ b R ρ k
  have hM : 0 ≤ M := by
    exact (integral_nonneg (fun z => by positivity)).trans
      (P.finiteInnerClusterComplexSource_fourthAbsoluteMoment_le hs hA.le hb hR hRmax
        hρ hρ1 hsmall N k S t hsupp)
  change ‖Q‖ ≤ cauchyContourNormBudget 5 (η : ℝ) M (d * radScale R ρ k) ‖Z‖ at hn
  have hn' := hn.trans (cauchyContourNormBudget_mono_length 5 (η : ℝ) hM
    (mul_pos hd hr) (norm_nonneg Z) hL)
  rw [mul_comm d, cauchyContourNormBudget_physical_scale 5 (η : ℝ) hM hr hd L] at hn'
  refine ⟨Q, hQ, (div_le_div_of_nonneg_right hn' (mul_pos hAk hr).le).trans_eq ?_⟩
  dsimp [M, finiteInnerClusterMassBudget]
  field_simp [hr.ne', hAk.ne', hb.ne', ne_of_gt (sub_pos.mpr ((div_lt_one hb).mpr hsmall))]
  <;> ring

end CircularMaterialTransferProfile
end Euler2D

end
