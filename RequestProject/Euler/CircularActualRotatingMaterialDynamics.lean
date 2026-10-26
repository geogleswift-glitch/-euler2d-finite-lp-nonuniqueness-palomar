module

public import RequestProject.Euler.RotatingNormalizedFiniteSelfVelocity
public import RequestProject.Euler.CircularFiniteActiveVelocityDecomposition
public import RequestProject.Euler.CircularFiniteAncestorPointwiseVelocity
public import RequestProject.Euler.NormalizedFiniteInnerVelocityBound
public import RequestProject.Euler.CircularFiniteEulerUniformVectorCorrection
public import RequestProject.Euler.ActualFinitePlanarSourceIdentity

/-! The original actual finite Euler velocity, in a rotating current
frame, is the singular material self velocity of that same label plus
the three explicit actual residuals. No current contour is assumed. -/

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

def rotatingNormalizedVelocityAt (A r Ω t θ : ℝ) (z : R2) : R2 :=
  planarRigidRotation (-θ) ((A * r)⁻¹ • particleVelocityRepresentative f S.backward S.backward_area
    t (r • planarRigidRotation θ z + torusCenter)) - (Ω / A) • perpJ z

theorem rotatingNormalizedParticleVelocity_eq_velocityAt (A r entrance Ω θentry τ : ℝ) (z : R2) :
    S.rotatingNormalizedParticleVelocity A r entrance Ω θentry τ z =
      S.rotatingNormalizedVelocityAt A r Ω (physicalTimeFromNormalized A entrance τ)
        (θentry + (Ω / A) * τ) z := rfl

end BoundedEulerParticleSystem

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def normalizedFiniteEulerResidual (s A₀ b R ρ : ℝ) (N k : ℕ) (hkN : k ≤ N)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t θ : ℝ) (z : R2) : R2 :=
  P.normalizedFiniteAncestorResidual s A₀ b R ρ N k hkN S t θ z +
    P.normalizedFiniteInnerVelocity s A₀ b R ρ N k S t θ z +
    S.normalizedCorrectionLabelVelocity (ampScale A₀ b k) (radScale R ρ k) t θ z

theorem actualFinite_rotating_velocity_eq_material_add_residual
    {s A₀ b R ρ q T entrance t a : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q)
    (N k : ℕ) (hkN : k ≤ N)
    (S : BoundedEulerParticleSystem
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T)
    (he : entrance ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T)
    (hentry : MeasurePreserving (S.backward entrance) volume volume)
    (htarget : MeasurePreserving (S.forward t) volume volume)
    (ha16 : a ≤ 1 / 16)
    (hsupp : ∀ y ∈ torusBox, a < ‖y - torusCenter‖ →
      S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t y = 0)
    (hlabel : boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N k) t) =
      fun y => P.finiteSinglePlanarInitialLabel s A₀ b R ρ N k (S.backward t (complexTorusPoint y)))
    (θentry θtarget : ℝ) (z : R2)
    (hchart : radScale R ρ k * ‖z‖ ≤ a)
    (hcore : ∀ j : Fin k, radScale R ρ k * ‖z‖ ≤ cellA * radScale R ρ j) :
    S.rotatingNormalizedVelocityAt (ampScale A₀ b k) (radScale R ρ k)
        (finiteAncestorAngularVelocity A₀ b k) t θtarget z =
      planarMaterialLabelVelocity kernelK
        (S.rotatingNormalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N k)
          (ampScale A₀ b k) (radScale R ρ k) θentry entrance)
        (S.rotatingNormalizedRelativeHomeomorph (radScale R ρ k) (radScale_pos hR hρ k).ne'
          entrance he t ht θentry θtarget) z +
      P.normalizedFiniteEulerResidual s A₀ b R ρ N k hkN S t θtarget z := by
  let A := ampScale A₀ b k
  let r := radScale R ρ k
  let Ω := finiteAncestorAngularVelocity A₀ b k
  let x := complexPhysicalPlane.symm (r • planarRigidRotation θtarget z)
  let w := P.finiteInitialPeriodicDensity s A₀ b R ρ N
  have hr : 0 < r := radScale_pos hR hρ k
  have hAk : 0 < A := div_pos hA (pow_pos hb k)
  have hxnorm : ‖x‖ = r * ‖z‖ := by
    dsimp only [x]
    rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      LinearIsometryEquiv.norm_map]
  have hxpoint : complexTorusPoint x = r • planarRigidRotation θtarget z + torusCenter := by
    dsimp only [complexTorusPoint, x]
    rw [LinearIsometryEquiv.apply_symm_apply]
  have hwf : w =ᵐ[μT] (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
      (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N : R2 → ℝ) := by
    filter_upwards [P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N,
      ae_restrict_mem measurableSet_torusBox] with y hy hybox
    exact (P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hybox).trans hy.symm
  let M := ∑ j ∈ Finset.range (N + 1), finiteLabelAmplitudeBound * ampScale A₀ b j
  have hwM : ∀ y, ‖w y‖ ≤ M := by
    intro y
    rw [show w y = ∑ j ∈ Finset.range (N + 1), P.finitePeriodicLabel s A₀ b R ρ N j y from
      P.finiteInitialPeriodicDensity_eq_sum_labels hs hR hRmax hρ hρ1 N y]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ =>
      (P.finitePeriodicLabel_bounds hs hA.le hb hR hRmax hρ hρ1 N j).2.2.1 y))
  have hOriginal := S.actualVelocity_eq_planar_add_correctionLabelField hwf hwM ha16 ht hsupp
    (x := x) (by simpa only [hxnorm] using hchart)
  have hSplit := P.velocityC_physicalFiniteDensity_eq_active_rigid_residual_cluster
    hs hA.le hb hR hRmax hρ hρ1 N k hkN S t
    (x := x) (by intro j; simpa only [hxnorm] using hcore j)
  dsimp only at hSplit
  dsimp only [w] at hOriginal
  rw [hSplit] at hOriginal
  have hReal := congrArg complexPhysicalPlane hOriginal
  simp only [map_add, ← complexPhysicalPlane_symm_eq_planeComplexEquiv,
    LinearIsometryEquiv.apply_symm_apply] at hReal
  rw [hxpoint] at hReal
  have hNormalized := congrArg
    (fun v : R2 => planarRigidRotation (-θtarget) ((A * r)⁻¹ • v)) hReal
  simp only [smul_add, map_add, map_sum, Finset.smul_sum] at hNormalized
  have hSelf : planarRigidRotation (-θtarget) ((A * r)⁻¹ • complexPhysicalPlane
      (velocityC (boxedComplexDensity (S.transportedScalar
        (P.finitePeriodicLabel s A₀ b R ρ N k) t)) x)) =
      planarMaterialLabelVelocity kernelK
        (S.rotatingNormalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N k)
          A r θentry entrance)
        (S.rotatingNormalizedRelativeHomeomorph r hr.ne' entrance he t ht θentry θtarget) z := by
    rw [hlabel]
    exact S.rotating_normalized_singlePlanar_velocity_eq_material
      (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N k) A hAk.ne' hr entrance he t ht hentry htarget θentry θtarget z
  have hRigid := rotating_normalized_rigid_velocity hAk.ne' hr.ne' Ω θtarget z
  change planarRigidRotation (-θtarget) ((A * r)⁻¹ •
      particleVelocityRepresentative _ S.backward S.backward_area t
        (r • planarRigidRotation θtarget z + torusCenter)) - (Ω / A) • perpJ z = _
  rw [hNormalized, hSelf, hRigid]
  change _ + (Ω / A) • perpJ z +
      P.normalizedFiniteAncestorResidual s A₀ b R ρ N k hkN S t θtarget z +
      P.normalizedFiniteInnerVelocity s A₀ b R ρ N k S t θtarget z +
      S.normalizedCorrectionLabelVelocity A r t θtarget z - (Ω / A) • perpJ z = _
  unfold normalizedFiniteEulerResidual
  abel

theorem eventually_actualFinite_rotating_velocity_eq_material_add_residual
    {s A₀ b q T B : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 ≤ T) (hB : 0 ≤ B) :
    ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      ∀ (N k : ℕ) (hkN : k ≤ N), ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hρ hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hρ hρ) N) T,
      (∀ u ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward u) volume volume ∧
        MeasurePreserving (S.backward u) volume volume) →
      ∀ entrance t : ℝ, ∀ he : entrance ∈ Icc (0 : ℝ) T, ∀ ht : t ∈ Icc (0 : ℝ) T,
      ∀ θentry θtarget : ℝ, ∀ z : R2, ‖z‖ ≤ B →
      S.rotatingNormalizedVelocityAt (ampScale A₀ b k) (radScale ρ ρ k)
          (finiteAncestorAngularVelocity A₀ b k) t θtarget z =
        planarMaterialLabelVelocity kernelK
          (S.rotatingNormalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b ρ ρ N k)
            (ampScale A₀ b k) (radScale ρ ρ k) θentry entrance)
          (S.rotatingNormalizedRelativeHomeomorph (radScale ρ ρ k) (radScale_pos hρ hρ k).ne'
            entrance he t ht θentry θtarget) z +
        P.normalizedFiniteEulerResidual s A₀ b ρ ρ N k hkN S t θtarget z := by
  obtain ⟨Cs, hCs, hsupport⟩ := P.exists_uniform_finiteEuler_support_bound
  obtain ⟨Cl, hCl, hlocalize⟩ := P.exists_uniform_actualFinite_boxed_label_eq_singlePlanar
  let d := max (B + 1) (2 + 2 * (Cs + Cl) * A₀ * T)
  have hd : 0 < d := (by linarith : (0 : ℝ) < B + 1).trans_le (le_max_left _ _)
  have hBd : B ≤ d := (by linarith : B ≤ B + 1).trans (le_max_left _ _)
  have hlarge : 2 + 2 * (Cs + Cl) * A₀ * T ≤ d := le_max_right _ _
  have hcatS : 0 ≤ Cs * A₀ * T := mul_nonneg (mul_nonneg hCs.le hA.le) hT
  have hcatL : 0 ≤ Cl * A₀ * T := mul_nonneg (mul_nonneg hCl.le hA.le) hT
  have hDriftS : 5 / 4 + Cs * A₀ * T < d := by nlinarith only [hlarge, hcatS, hcatL]
  have hDriftL : 5 / 4 + Cl * A₀ * T < d := by nlinarith only [hlarge, hcatS, hcatL]
  have he : Tendsto (fun ξ : ℝ => Real.exp (-ξ)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hden : Tendsto (fun ξ : ℝ => 1 - Real.exp (-ξ) / b) atTop (𝓝 1) := by
    simpa only [zero_div, sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ξ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub (he.div_const b)
  have hDriftLimit (C : ℝ) : Tendsto (fun ξ : ℝ => 5 / 4 +
      (C * A₀ / (1 - Real.exp (-ξ) / b)) * T) atTop (𝓝 (5 / 4 + C * A₀ * T)) := by
    have hnum : Tendsto (fun _ξ : ℝ => C * A₀) atTop (𝓝 (C * A₀)) := tendsto_const_nhds
    simpa only [Pi.div_def, div_one] using
      ((hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)).mul_const T).const_add (5 / 4)
  have hRadiusLimit : Tendsto (fun ξ : ℝ => d * Real.exp (-ξ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul d
  have hCoreLimit : Tendsto (fun ξ : ℝ => B * Real.exp (-ξ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul B
  filter_upwards [he.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    he.eventually (eventually_lt_nhds hb),
    (hDriftLimit Cs).eventually (eventually_lt_nhds hDriftS),
    (hDriftLimit Cl).eventually (eventually_lt_nhds hDriftL),
    hRadiusLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    hCoreLimit.eventually (eventually_lt_nhds cellA_pos)]
    with ξ hhalf hρb hDriftSξ hDriftLξ hdρ hBρ
  try dsimp only
  let ρ := Real.exp (-ξ)
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hρ1 : ρ ≤ 1 := hhalf.le.trans (by norm_num)
  have hdρ1 : d * ρ < 1 := hdρ.trans (by norm_num : (1 / 16 : ℝ) < 1)
  intro N k hkN S harea entrance t he ht θentry θtarget z hz
  have hsupp := hsupport (s := s) (A₀ := A₀) (b := b) (R := ρ) (ρ := ρ) (q := q)
    (T := T) (H := T) (c := d) hs hA.le hb hρ hhalf.le hρ hρ1 hρb hq hqE hT le_rfl
    hDriftSξ hdρ1 N S t ht
  have hlabel := hlocalize (s := s) (A₀ := A₀) (b := b) (R := ρ) (ρ := ρ) (q := q)
    (T := T) (H := T) (c := d) hs hA.le hb hρ hhalf.le hρ hρ1 hρb hq hqE hT le_rfl
    hDriftLξ hdρ1 N S t ht k
  have hquery : radScale ρ ρ k * ‖z‖ ≤ d * ρ := by
    have hrk : 0 ≤ radScale ρ ρ k := (radScale_pos hρ hρ k).le
    have hrkmax : radScale ρ ρ k ≤ ρ := mul_le_of_le_one_right hρ.le (pow_le_one₀ hρ.le hρ1)
    calc
      _ ≤ radScale ρ ρ k * d := mul_le_mul_of_nonneg_left (hz.trans hBd) hrk
      _ ≤ ρ * d := mul_le_mul_of_nonneg_right hrkmax hd.le
      _ = _ := mul_comm _ _
  have hcore (j : Fin k) : radScale ρ ρ k * ‖z‖ ≤ cellA * radScale ρ ρ j := by
    have hrj : 0 < radScale ρ ρ j := radScale_pos hρ hρ j
    have hrk : 0 ≤ radScale ρ ρ k := (radScale_pos hρ hρ k).le
    have hratio := radScale_ratio_eq_pow hρ.ne' hρ.ne' j.isLt.le
    have hp : ρ ^ (k - (j : ℕ)) ≤ ρ := by
      simpa only [pow_one] using pow_le_pow_of_le_one hρ.le hρ1 (show 1 ≤ k - (j : ℕ) by omega)
    have hrad : radScale ρ ρ k ≤ ρ * radScale ρ ρ j := (div_le_iff₀ hrj).mp (hratio.trans_le hp)
    have hsep := mul_le_mul_of_nonneg_right hBρ.le hrj.le
    calc
      _ ≤ radScale ρ ρ k * B := mul_le_mul_of_nonneg_left hz hrk
      _ ≤ (ρ * radScale ρ ρ j) * B := mul_le_mul_of_nonneg_right hrad hB
      _ ≤ _ := by nlinarith only [hsep]
  exact P.actualFinite_rotating_velocity_eq_material_add_residual hs hA hb hρ hhalf.le hρ hρ1 hq hqE
    N k hkN S he ht (harea entrance he).2 (harea t ht).1 hdρ.le hsupp hlabel θentry θtarget z hquery hcore

theorem eventually_actualFinite_normalizedEulerResidual_le
    {s A₀ b q T c C₀ K B ε : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b) (hb1 : b ≤ 1)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 ≤ T)
    (hc : 0 < c) (hC₀ : 0 < C₀) (hK : 0 ≤ K) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      ∀ (N k : ℕ) (hkN : k ≤ N), ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hρ hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hρ hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S → ∀ t ∈ Icc (0 : ℝ) T,
      ∀ {δ : ℝ} (G : ∀ j : Fin k, P.FiniteOuterMaterialTube s ρ ρ N
        (finiteAncestorPointwiseIndex hkN j) S t c δ),
      (∀ (j : Fin k) i,
        let l := finiteAncestorPointwiseIndex hkN j
        ‖contourParameterShiftC1 ((G j).shifts (l, i)) ((G j).contours (l, i)) -
          (G j).reference (l, i)‖ ≤ radScale ρ ρ j * ((C₀ * ρ ^ 6) ^ (k - (j : ℕ)) * K)) →
      ∀ θ : ℝ, ∀ z : R2, ‖z‖ ≤ B →
        ‖P.normalizedFiniteEulerResidual s A₀ b ρ ρ N k hkN S t θ z‖ ≤ ε := by
  have hε3 : 0 < ε / 3 := div_pos hε (by norm_num)
  have hancestor := P.eventually_normalizedFiniteAncestorResidual_le hb hb1 hc hC₀ hK hB hε3
  have hinner := P.eventually_normalizedFiniteInnerVelocity_le hb hε3
  have htorus := P.eventually_actualFinite_normalizedCorrectionLabelVelocity_le hs hA hb hb1 hq hqE hT hB hε3
  have he := Real.tendsto_exp_neg_atTop_nhds_zero
  filter_upwards [hancestor, hinner, htorus,
    he.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with ξ ha hi hcorr hhalf
  try dsimp only at ha hi hcorr ⊢
  let ρ := Real.exp (-ξ)
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  intro N k hkN S hS t ht δ G hql θ z hz
  have ha' := ha (s := s) (A₀ := A₀) (R := ρ) hs hA hρ hhalf.le N k hkN S t ht G hql θ z hz
  have hi' := hi (s := s) (A₀ := A₀) (R := ρ) hs hA hρ hhalf.le N k S t θ z
  have hc' := hcorr N S hS t ht k θ z hz
  unfold normalizedFiniteEulerResidual
  calc
    _ ≤ ‖P.normalizedFiniteAncestorResidual s A₀ b ρ ρ N k hkN S t θ z‖ +
        ‖P.normalizedFiniteInnerVelocity s A₀ b ρ ρ N k S t θ z‖ +
        ‖S.normalizedCorrectionLabelVelocity (ampScale A₀ b k) (radScale ρ ρ k) t θ z‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ε := by linarith only [ha', hi', hc']

theorem eventually_actualFinite_rotating_particle_material_equation
    {s A₀ b q T B : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 ≤ T) (hB : 0 ≤ B) :
    ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      ∀ (N k : ℕ) (hkN : k ≤ N), ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hρ hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hρ hρ) N) T,
      (∀ u ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward u) volume volume ∧
        MeasurePreserving (S.backward u) volume volume) →
      ∀ entrance : ℝ, ∀ he : entrance ∈ Icc (0 : ℝ) T, ∀ θentry : ℝ, ∀ a : R2, ∀ τ : ℝ,
      let A := ampScale A₀ b k
      let r := radScale ρ ρ k
      let Ω := finiteAncestorAngularVelocity A₀ b k
      let t := physicalTimeFromNormalized A entrance τ
      let θ := θentry + (Ω / A) * τ
      let Z := S.rotatingNormalizedRelativeParticleCurve A r entrance Ω θentry a
      ∀ ht : t ∈ Icc (0 : ℝ) T, ‖Z τ‖ ≤ B →
        HasDerivAt Z
          (planarMaterialLabelVelocity kernelK
            (S.rotatingNormalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b ρ ρ N k)
              A r θentry entrance)
            (S.rotatingNormalizedRelativeHomeomorph r (radScale_pos hρ hρ k).ne'
              entrance he t ht θentry θ) (Z τ) +
            P.normalizedFiniteEulerResidual s A₀ b ρ ρ N k hkN S t θ (Z τ)) τ := by
  have hfield := P.eventually_actualFinite_rotating_velocity_eq_material_add_residual hs hA hb hq hqE hT hB
  filter_upwards [hfield] with ξ hξ
  try dsimp only at hξ ⊢
  let ρ := Real.exp (-ξ)
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  intro N k hkN S harea entrance he θentry a τ
  try dsimp only
  intro ht hbound
  have hd := S.rotatingNormalizedRelativeParticleCurve_hasDerivAt_velocity
    (ampScale A₀ b k) (radScale ρ ρ k) entrance (finiteAncestorAngularVelocity A₀ b k) θentry
    (radScale_pos hρ hρ k).ne' a ht
  rw [S.rotatingNormalizedParticleVelocity_eq_velocityAt] at hd
  rw [hξ N k hkN S harea entrance _ he ht θentry _ _ hbound] at hd
  exact hd

theorem eventually_actualFinite_rotating_material_velocity_error_le
    {s A₀ b q T c C₀ K B ε : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b) (hb1 : b ≤ 1)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 ≤ T)
    (hc : 0 < c) (hC₀ : 0 < C₀) (hK : 0 ≤ K) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      ∀ (N k : ℕ) (hkN : k ≤ N), ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hρ hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hρ hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      (∀ u ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward u) volume volume ∧
        MeasurePreserving (S.backward u) volume volume) →
      ∀ entrance t : ℝ, ∀ he : entrance ∈ Icc (0 : ℝ) T, ∀ ht : t ∈ Icc (0 : ℝ) T,
      ∀ {δ : ℝ} (G : ∀ j : Fin k, P.FiniteOuterMaterialTube s ρ ρ N
        (finiteAncestorPointwiseIndex hkN j) S t c δ),
      (∀ (j : Fin k) i,
        let l := finiteAncestorPointwiseIndex hkN j
        ‖contourParameterShiftC1 ((G j).shifts (l, i)) ((G j).contours (l, i)) -
          (G j).reference (l, i)‖ ≤ radScale ρ ρ j * ((C₀ * ρ ^ 6) ^ (k - (j : ℕ)) * K)) →
      ∀ θentry θtarget : ℝ, ∀ z : R2, ‖z‖ ≤ B →
        ‖S.rotatingNormalizedVelocityAt (ampScale A₀ b k) (radScale ρ ρ k)
            (finiteAncestorAngularVelocity A₀ b k) t θtarget z -
          planarMaterialLabelVelocity kernelK
            (S.rotatingNormalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b ρ ρ N k)
              (ampScale A₀ b k) (radScale ρ ρ k) θentry entrance)
            (S.rotatingNormalizedRelativeHomeomorph (radScale ρ ρ k) (radScale_pos hρ hρ k).ne'
              entrance he t ht θentry θtarget) z‖ ≤ ε := by
  have hfield := P.eventually_actualFinite_rotating_velocity_eq_material_add_residual hs hA hb hq hqE hT hB
  have herror := P.eventually_actualFinite_normalizedEulerResidual_le hs hA hb hb1 hq hqE hT hc hC₀ hK hB hε
  filter_upwards [hfield, herror] with ξ hξ hεξ
  try dsimp only at hξ hεξ ⊢
  intro N k hkN S hS harea entrance t he ht δ G hql θentry θtarget z hz
  rw [hξ N k hkN S harea entrance t he ht θentry θtarget z hz, add_sub_cancel_left]
  exact hεξ N k hkN S hS t ht G hql θtarget z hz

end CircularMaterialTransferProfile
end Euler2D

end
