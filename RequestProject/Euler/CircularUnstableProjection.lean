module

public import RequestProject.Euler.ContourFourthModeProjection
public import RequestProject.Euler.CircularFourierLinearFlow
public import RequestProject.Euler.Transfer

/-! A genuine bounded real projection onto the two-dimensional growing
plane in the original little contour family Banach space. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff ComplexConjugate

namespace Euler2D

local instance (priority := 2000) unstableProjectionLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) unstableProjectionLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) unstableProjectionFamily_smulComm (γ : ℝ≥0) :
    SMulCommClass ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_comm a b H := by
    funext i
    change a • (b • H i) = b • (a • H i)
    rw [smul_smul, smul_smul]
    exact congrArg (fun s : ℝ => s • H i) (mul_comm a b)

def circularEllPlusCLM : (Fin 2 → ℂ) →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ) ((2 : ℂ)⁻¹)).comp (ContinuousLinearMap.proj 0) +
    ((ContinuousLinearMap.mul ℝ ℂ) ((2 * I * cellA : ℂ)⁻¹)).comp (ContinuousLinearMap.proj 1)

theorem circularEllPlusCLM_apply (η : Fin 2 → ℂ) : circularEllPlusCLM η = ellPlus η := by
  change (2 : ℂ)⁻¹ * η 0 + (2 * I * cellA : ℂ)⁻¹ * η 1 = _
  unfold ellPlus
  simp only [div_eq_mul_inv]
  ring

theorem ellPlus_complex_smul (c : ℂ) (η : Fin 2 → ℂ) :
    ellPlus (c • η) = c * ellPlus η := by
  simp only [ellPlus, Pi.smul_apply, smul_eq_mul]
  ring

/-- The actual growing coordinate, extracted from the original contour
by the bounded fourth Fourier normal coefficient and the true left eigenvector. -/
def circularUnstableCoordinateCLM (γ : ℝ≥0) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] ℂ :=
  circularEllPlusCLM.comp (circularFourthNormalCoefficientCLM γ)

/-- The genuine full growing perturbation, including its tangential component. -/
def circularUnstableEmbeddingCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ℂ →L[ℝ] (Fin 2 → LittleContourSpace γ) :=
  ContinuousLinearMap.pi fun i =>
    (littleContourFourierModeCLM hγ hγ1 5).comp
      ((ContinuousLinearMap.mul ℝ ℂ)
        (circularNormalModePlus (circularContourRadii i) (vPlus i) (circularGrowingTangent i))) +
    (littleContourFourierModeCLM hγ hγ1 (-3)).comp
      (((ContinuousLinearMap.mul ℝ ℂ)
        (circularNormalModeMinus (circularContourRadii i) (vPlus i) (circularGrowingTangent i))).comp
          Complex.conjCLE.toContinuousLinearMap)

theorem circularUnstableEmbeddingCLM_apply {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (c : ℂ) :
    circularUnstableEmbeddingCLM hγ hγ1 c =
      circularNormalModeLittle hγ hγ1 2 (c • vPlus) (c • circularGrowingTangent) := by
  funext i
  change littleContourFourierModeCLM hγ hγ1 5
      (circularNormalModePlus (circularContourRadii i) (vPlus i) (circularGrowingTangent i) * c) +
    littleContourFourierModeCLM hγ hγ1 (-3)
      (circularNormalModeMinus (circularContourRadii i) (vPlus i) (circularGrowingTangent i) * conj c) = _
  simp only [littleContourFourierModeCLM_apply]
  change _ = littleContourFourierMode hγ hγ1 5
      (circularNormalModePlus (circularContourRadii i) ((c • vPlus) i) ((c • circularGrowingTangent) i)) +
    littleContourFourierMode hγ hγ1 (-3)
      (circularNormalModeMinus (circularContourRadii i) ((c • vPlus) i) ((c • circularGrowingTangent) i))
  congr 1
  · congr 1
    simp only [circularNormalModePlus, Pi.smul_apply, smul_eq_mul]
    ring
  · congr 1
    simp only [circularNormalModeMinus, Pi.smul_apply, smul_eq_mul, map_mul]
    ring

theorem circularUnstableCoordinate_embedding {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (c : ℂ) :
    circularUnstableCoordinateCLM γ (circularUnstableEmbeddingCLM hγ hγ1 c) = c := by
  change circularEllPlusCLM
    (circularFourthNormalCoefficientCLM γ (circularUnstableEmbeddingCLM hγ hγ1 c)) = c
  rw [circularUnstableEmbeddingCLM_apply, circularFourthNormalCoefficientCLM_normalMode,
    circularEllPlusCLM_apply, ellPlus_complex_smul, ellPlus_vPlus, mul_one]

theorem circularUnstableEmbeddingCLM_injective {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) : Function.Injective (circularUnstableEmbeddingCLM hγ hγ1) := by
  intro c d hcd
  have h := congrArg (circularUnstableCoordinateCLM γ) hcd
  simpa only [circularUnstableCoordinate_embedding] using h

def circularUnstableProjectionCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ) :=
  (circularUnstableEmbeddingCLM hγ hγ1).comp (circularUnstableCoordinateCLM γ)

def circularUnstableSpace {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    Submodule ℝ (Fin 2 → LittleContourSpace γ) :=
  (circularUnstableEmbeddingCLM hγ hγ1).toLinearMap.range

theorem circularUnstableProjectionCLM_apply {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ) :
    circularUnstableProjectionCLM hγ hγ1 H =
      circularUnstableEmbeddingCLM hγ hγ1 (circularUnstableCoordinateCLM γ H) := rfl

theorem circularUnstableProjectionCLM_embedding {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (c : ℂ) :
    circularUnstableProjectionCLM hγ hγ1 (circularUnstableEmbeddingCLM hγ hγ1 c) =
      circularUnstableEmbeddingCLM hγ hγ1 c := by
  change circularUnstableEmbeddingCLM hγ hγ1
    (circularUnstableCoordinateCLM γ (circularUnstableEmbeddingCLM hγ hγ1 c)) = _
  rw [circularUnstableCoordinate_embedding]

theorem circularUnstableProjectionCLM_idempotent {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ) :
    circularUnstableProjectionCLM hγ hγ1 (circularUnstableProjectionCLM hγ hγ1 H) =
      circularUnstableProjectionCLM hγ hγ1 H := by
  rw [circularUnstableProjectionCLM_apply hγ hγ1 H,
    circularUnstableProjectionCLM_embedding]

theorem mem_circularUnstableSpace_iff {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (H : Fin 2 → LittleContourSpace γ) :
    H ∈ circularUnstableSpace hγ hγ1 ↔ circularUnstableProjectionCLM hγ hγ1 H = H := by
  constructor
  · rintro ⟨c, rfl⟩
    exact circularUnstableProjectionCLM_embedding hγ hγ1 c
  · intro hH
    exact ⟨circularUnstableCoordinateCLM γ H, hH⟩

theorem range_circularUnstableProjectionCLM {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (circularUnstableProjectionCLM hγ hγ1).toLinearMap.range = circularUnstableSpace hγ hγ1 := by
  ext H
  constructor
  · rintro ⟨G, rfl⟩
    exact ⟨circularUnstableCoordinateCLM γ G, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨circularUnstableEmbeddingCLM hγ hγ1 c, circularUnstableProjectionCLM_embedding hγ hγ1 c⟩

theorem isClosed_circularUnstableSpace {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    IsClosed (circularUnstableSpace hγ hγ1 : Set (Fin 2 → LittleContourSpace γ)) := by
  have he : (circularUnstableSpace hγ hγ1 : Set (Fin 2 → LittleContourSpace γ)) =
      {H | circularUnstableProjectionCLM hγ hγ1 H = H} := by
    ext H
    exact mem_circularUnstableSpace_iff hγ hγ1 H
  rw [he]
  exact isClosed_eq (circularUnstableProjectionCLM hγ hγ1).continuous continuous_id

theorem isClosed_ker_circularUnstableProjectionCLM {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    IsClosed ((circularUnstableProjectionCLM hγ hγ1).ker : Set (Fin 2 → LittleContourSpace γ)) :=
  (circularUnstableProjectionCLM hγ hγ1).isClosed_ker

theorem isCompl_circularUnstableSpace_ker {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    IsCompl (circularUnstableSpace hγ hγ1) (circularUnstableProjectionCLM hγ hγ1).ker := by
  have hp : IsIdempotentElem (circularUnstableProjectionCLM hγ hγ1).toLinearMap := by
    apply LinearMap.ext
    intro H
    exact circularUnstableProjectionCLM_idempotent hγ hγ1 H
  have hi := LinearMap.IsIdempotentElem.isCompl hp
  rw [range_circularUnstableProjectionCLM] at hi
  exact hi

set_option maxHeartbeats 600000 in
def circularUnstableEquiv {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ℂ ≃L[ℝ] circularUnstableSpace hγ hγ1 where
  toLinearEquiv :=
    { toFun := fun c => ⟨circularUnstableEmbeddingCLM hγ hγ1 c, ⟨c, rfl⟩⟩
      invFun := fun H => circularUnstableCoordinateCLM γ H.val
      left_inv := circularUnstableCoordinate_embedding hγ hγ1
      right_inv := fun H => by
        apply Subtype.ext
        change circularUnstableEmbeddingCLM hγ hγ1
          (circularUnstableCoordinateCLM γ H.val) = H.val
        have he := (mem_circularUnstableSpace_iff hγ hγ1 H.val).mp H.property
        rw [circularUnstableProjectionCLM_apply] at he
        exact he
      map_add' := fun c d => Subtype.ext (map_add (circularUnstableEmbeddingCLM hγ hγ1) c d)
      map_smul' := fun a c => Subtype.ext (map_smul (circularUnstableEmbeddingCLM hγ hγ1) a c) }
  continuous_toFun := (circularUnstableEmbeddingCLM hγ hγ1).continuous.subtype_mk _
  continuous_invFun := (circularUnstableCoordinateCLM γ).continuous.comp continuous_subtype_val

theorem finrank_circularUnstableSpace {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) : Module.finrank ℝ (circularUnstableSpace hγ hγ1) = 2 := by
  calc
    Module.finrank ℝ (circularUnstableSpace hγ hγ1) = Module.finrank ℝ ℂ :=
      (circularUnstableEquiv hγ hγ1).symm.toLinearEquiv.finrank_eq
    _ = 2 := Complex.finrank_real_complex

theorem circularUnstableSpace_mem_fourfold_area {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {H : Fin 2 → LittleContourSpace γ}
    (hH : H ∈ circularUnstableSpace hγ hγ1) (i : Fin 2) :
    H i ∈ fourfoldLittleContourSubmodule γ ⊓ LittleContourAreaConstraint γ (circularContourRadii i) := by
  rcases hH with ⟨c, hc⟩
  change circularUnstableEmbeddingCLM hγ hγ1 c = H at hc
  have he : H = circularNormalModeLittle hγ hγ1 2 (c • vPlus) (c • circularGrowingTangent) :=
    hc.symm.trans (circularUnstableEmbeddingCLM_apply hγ hγ1 c)
  rw [he]
  exact circularFourthModeLittle_mem_fourfold_area hγ hγ1 _ _ i

theorem circularAmplitudeGeneratorComplex_unstable (c : ℂ) :
    circularAmplitudeGeneratorComplex 2 (c • vPlus, c • circularGrowingTangent) =
      lamStar • (c • vPlus, c • circularGrowingTangent) := by
  change circularAmplitudeGenerator 2 (c • vPlus, c • circularGrowingTangent) = _
  rw [circularAmplitudeGenerator_apply]
  change (circularAngularNormalAmplitude 2 (c • vPlus),
      circularAngularTangentialAmplitude 2 (c • vPlus) (c • circularGrowingTangent)) =
    (lamStar • (c • vPlus), lamStar • (c • circularGrowingTangent))
  apply Prod.ext
  · change circularAngularNormalAmplitude 2 (c • vPlus) = lamStar • (c • vPlus)
    have hn : circularAngularNormalAmplitude 2 vPlus = lamStar • vPlus := iB4_vPlus
    rw [circularAngularNormalAmplitude_smul, hn, smul_smul, smul_smul, mul_comm c lamStar]
  · change circularAngularTangentialAmplitude 2 (c • vPlus) (c • circularGrowingTangent) =
      lamStar • (c • circularGrowingTangent)
    rw [circularAngularTangentialAmplitude_smul, circularGrowingTangent_equation,
      smul_smul, smul_smul, mul_comm c lamStar]

def circularUnstableAmplitudeCurve (c : ℂ) (t : ℝ) : CircularFourierAmplitudes :=
  exp ((t : ℂ) * lamStar) • (c • vPlus, c • circularGrowingTangent)

theorem circularUnstableAmplitudeCurve_hasDerivAt (c : ℂ) (t : ℝ) :
    HasDerivAt (circularUnstableAmplitudeCurve c)
      (circularAmplitudeGenerator 2 (circularUnstableAmplitudeCurve c t)) t := by
  have hd := (hasDerivAt_circularGrowingScalar t).smul_const
    (c • vPlus, c • circularGrowingTangent)
  change HasDerivAt (circularUnstableAmplitudeCurve c)
    (circularAmplitudeGeneratorComplex 2
      (exp ((t : ℂ) * lamStar) • (c • vPlus, c • circularGrowingTangent))) t
  rw [map_smul, circularAmplitudeGeneratorComplex_unstable, smul_smul]
  convert hd using 1 <;> congr 1 <;> ring

theorem circularUnstableAmplitudeCurve_zero (c : ℂ) :
    circularUnstableAmplitudeCurve c 0 = (c • vPlus, c • circularGrowingTangent) := by
  simp only [circularUnstableAmplitudeCurve, Complex.ofReal_zero, zero_mul, exp_zero, one_smul]

theorem circularUnstableAmplitudeCurve_period (c : ℂ) :
    circularUnstableAmplitudeCurve c period =
      (-lamMult : ℝ) • (c • vPlus, c • circularGrowingTangent) := by
  rw [circularUnstableAmplitudeCurve, period_multipliers_m4.1]
  apply Prod.ext <;> funext i <;>
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
      Complex.real_smul, Complex.ofReal_neg]

theorem circularAmplitudeLinearFlow_unstable (c : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    circularAmplitudeLinearFlow 2 (c • vPlus, c • circularGrowingTangent) t =
      circularUnstableAmplitudeCurve c t := by
  have hαc : Continuous (circularAmplitudeLinearFlow 2 (c • vPlus, c • circularGrowingTangent)) :=
    continuous_iff_continuousAt.mpr
      (fun s => (circularAmplitudeLinearFlow_hasDerivAt 2 (c • vPlus, c • circularGrowingTangent) s).continuousAt)
  have hβc : Continuous (circularUnstableAmplitudeCurve c) :=
    continuous_iff_continuousAt.mpr (fun s => (circularUnstableAmplitudeCurve_hasDerivAt c s).continuousAt)
  have he : EqOn (circularAmplitudeLinearFlow 2 (c • vPlus, c • circularGrowingTangent))
      (circularUnstableAmplitudeCurve c) (Icc (0 : ℝ) t) :=
    ODE_solution_unique_of_mem_Icc_right
      (v := fun _ z => circularAmplitudeGenerator 2 z)
      (s := fun _ => (univ : Set CircularFourierAmplitudes))
      (fun _ _ => (circularAmplitudeGenerator 2).lipschitz.lipschitzOnWith)
      hαc.continuousOn
      (fun s _ => (circularAmplitudeLinearFlow_hasDerivAt 2 (c • vPlus, c • circularGrowingTangent) s).hasDerivWithinAt)
      (fun _ _ => mem_univ _)
      hβc.continuousOn
      (fun s _ => (circularUnstableAmplitudeCurve_hasDerivAt c s).hasDerivWithinAt)
      (fun _ _ => mem_univ _)
      (by rw [circularAmplitudeLinearFlow_zero, circularUnstableAmplitudeCurve_zero])
  exact he ⟨ht, le_rfl⟩

theorem circularAmplitudeLinearFlow_unstable_period (c : ℂ) :
    circularAmplitudeLinearFlow 2 (c • vPlus, c • circularGrowingTangent) period =
      (-lamMult : ℝ) • (c • vPlus, c • circularGrowingTangent) := by
  rw [circularAmplitudeLinearFlow_unstable c (show 0 ≤ period by unfold period; positivity),
    circularUnstableAmplitudeCurve_period]

theorem circularPeriod_derivative_unstableEmbedding {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X) (c : ℂ) :
    fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
      (circularUnstableEmbeddingCLM hγ hγ1.le c) =
      (-lamMult : ℝ) • circularUnstableEmbeddingCLM hγ hγ1.le c := by
  have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
  change fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
      (circularUnstableEmbeddingCLM hγ hγle c) =
    (-lamMult : ℝ) • circularUnstableEmbeddingCLM hγ hγle c
  have hp := circularAmplitudeLinearFlow_unstable_period c
  have hn : circularNormalLinearFlow 2 (c • vPlus) period = (-lamMult : ℝ) • (c • vPlus) := by
    rw [← circularAmplitudeLinearFlow_normal 2 (c • vPlus, c • circularGrowingTangent)
      (show 0 ≤ period by unfold period; positivity)]
    exact congrArg Prod.fst hp
  have hτ : (circularAmplitudeLinearFlow 2 (c • vPlus, c • circularGrowingTangent) period).2 =
      (-lamMult : ℝ) • (c • circularGrowingTangent) := congrArg Prod.snd hp
  have hf : fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
      (circularNormalModeLittle hγ hγle 2 (c • vPlus) (c • circularGrowingTangent)) =
    circularNormalModeLittle hγ hγle 2 (circularNormalLinearFlow 2 (c • vPlus) period)
      (circularAmplitudeLinearFlow 2 (c • vPlus, c • circularGrowingTangent) period).2 :=
    circularPeriod_derivative_Fourier_block hγ hγ1 hρ hX 2 (c • vPlus) (c • circularGrowingTangent)
  rw [circularUnstableEmbeddingCLM_apply hγ hγle c, hf, hn, hτ,
    circularNormalModeLittle_real_smul hγ hγle 2]

theorem circularPeriod_derivative_on_unstableSpace {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    {H : Fin 2 → LittleContourSpace γ} (hH : H ∈ circularUnstableSpace hγ hγ1.le) :
    fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) H = (-lamMult : ℝ) • H := by
  rcases hH with ⟨c, rfl⟩
  exact circularPeriod_derivative_unstableEmbedding hγ hγ1 hρ hX c

theorem circularPeriod_derivative_unstableProjection_apply {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (H : Fin 2 → LittleContourSpace γ) :
    fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
    (circularUnstableProjectionCLM hγ hγ1.le H) =
      (-lamMult : ℝ) • circularUnstableProjectionCLM hγ hγ1.le H := by
  have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
  change fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
      (circularUnstableProjectionCLM hγ hγle H) =
    (-lamMult : ℝ) • circularUnstableProjectionCLM hγ hγle H
  rw [circularUnstableProjectionCLM_apply hγ hγle H]
  exact circularPeriod_derivative_unstableEmbedding hγ hγ1 hρ hX _

instance finiteDimensional_circularUnstableSpace {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) : FiniteDimensional ℝ (circularUnstableSpace hγ hγ1) :=
  FiniteDimensional.of_injective
    (circularUnstableEquiv hγ hγ1).symm.toLinearEquiv.toLinearMap
    (circularUnstableEquiv hγ hγ1).symm.injective

instance completeSpace_circularUnstableSpace {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) : CompleteSpace (circularUnstableSpace hγ hγ1) :=
  (isClosed_circularUnstableSpace hγ hγ1).completeSpace_coe

theorem circularUnstableEmbeddingCLM_one {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    circularUnstableEmbeddingCLM hγ hγ1.le 1 = circularGrowingVariation hγ hγ1 0 := by
  have hγle : γ ≤ 1 := by exact_mod_cast hγ1.le
  change circularUnstableEmbeddingCLM hγ hγle 1 = circularGrowingVariation hγ hγ1 0
  have hz : circularGrowingVariation hγ hγ1 0 =
      circularNormalModeLittle hγ hγle 2 vPlus circularGrowingTangent :=
    circularGrowingVariation_zero hγ hγ1
  rw [circularUnstableEmbeddingCLM_apply hγ hγle 1, hz]
  simp only [one_smul]

theorem circularPeriod_derivative_unstable_norm {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    {H : Fin 2 → LittleContourSpace γ} (hH : H ∈ circularUnstableSpace hγ hγ1.le) :
    ‖fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1) H‖ = lamMult * ‖H‖ := by
  rw [circularPeriod_derivative_on_unstableSpace hγ hγ1 hρ hX hH,
    norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (lt_trans zero_lt_one one_lt_lamMult)]

end Euler2D

end
