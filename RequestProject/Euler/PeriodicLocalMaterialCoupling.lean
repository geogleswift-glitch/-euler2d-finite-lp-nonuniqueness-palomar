module

public import RequestProject.Euler.PeriodicLocalCoupledKernelSplit

/-! Actual weighted material coupling for the periodic singular
local kernel. Position comparisons are required only on source
labels carrying nonzero initial vorticity. -/

@[expose] public section

set_option maxHeartbeats 4500000

noncomputable section

open MeasureTheory Set Filter Topology Metric Real

namespace Euler2D

theorem integrable_periodicKernel_material {F : Type*} [NormedAddCommGroup F]
    {K : R2 → F} (hK : Integrable K μT) (hp : IsTorusPeriodic K)
    {X : R2 → R2} (hX : TorusAreaPreserving X) (x : R2) :
    Integrable (fun b => K ((x + torusCenter) - X b)) μT := by
  have hg := (torusAreaPreserving_sub_left (x + torusCenter)).integrable_comp hK hp
  exact hX.integrable_comp hg (isTorusPeriodic_comp_sub_left hp _)

theorem integral_norm_periodicKernel_material {F : Type*} [NormedAddCommGroup F]
    {K : R2 → F} (hK : Integrable K μT) (hp : IsTorusPeriodic K)
    {X : R2 → R2} (hX : TorusAreaPreserving X) (x : R2) :
    (∫ b in torusBox, ‖K ((x + torusCenter) - X b)‖) = ∫ z in torusBox, ‖K z‖ := by
  have hn : IsTorusPeriodic (fun z => ‖K z‖) := fun z i => congrArg norm (hp z i)
  have hg := (torusAreaPreserving_sub_left (x + torusCenter)).integrable_comp hK.norm hn
  calc
    _ = ∫ b in torusBox, ‖K ((x + torusCenter) - b)‖ :=
      hX.integral_comp hg.aestronglyMeasurable (isTorusPeriodic_comp_sub_left hn _)
    _ = _ := (torusAreaPreserving_sub_left (x + torusCenter)).integral_comp hK.norm.aestronglyMeasurable hn

def periodicLocalMaterialVelocity (w : R2 → ℝ) (X : R2 → R2) (x : R2) : R2 :=
  ∫ b in torusBox, w b • periodicLocalKernel ((x + torusCenter) - X b)

theorem integrable_periodicLocalMaterial_integrand {w : R2 → ℝ} {B : ℝ}
    (hw : Integrable w μT) (hB : ∀ᵐ b ∂μT, ‖w b‖ ≤ B)
    {X : R2 → R2} (hX : TorusAreaPreserving X) (x : R2) :
    Integrable (fun b => w b • periodicLocalKernel ((x + torusCenter) - X b)) μT :=
  (integrable_periodicKernel_material integrable_periodicLocalKernel isTorusPeriodic_periodicLocalKernel hX x).bdd_smul
    B hw.aestronglyMeasurable hB

theorem norm_periodicLocalMaterialVelocity_le {w : R2 → ℝ} {B : ℝ}
    (hB : ∀ᵐ b ∂μT, ‖w b‖ ≤ B) {X : R2 → R2} (hX : TorusAreaPreserving X) (x : R2) :
    ‖periodicLocalMaterialVelocity w X x‖ ≤ B * ∫ z in torusBox, ‖periodicLocalKernel z‖ := by
  unfold periodicLocalMaterialVelocity
  calc
    _ ≤ ∫ b in torusBox, B * ‖periodicLocalKernel ((x + torusCenter) - X b)‖ := by
      apply norm_integral_le_of_norm_le
        ((integrable_periodicKernel_material integrable_periodicLocalKernel
          isTorusPeriodic_periodicLocalKernel hX x).norm.const_mul B)
      filter_upwards [hB] with b hb
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = _ := by rw [integral_const_mul, integral_norm_periodicKernel_material integrable_periodicLocalKernel
      isTorusPeriodic_periodicLocalKernel hX x]

theorem norm_periodicLocalMaterial_sub_le_raw
    {w : R2 → ℝ} {B C h : ℝ} (hw : Integrable w μT) (hB0 : 0 ≤ B)
    (hB : ∀ᵐ b ∂μT, ‖w b‖ ≤ B) (hC : 0 ≤ C)
    (hderiv : ∀ z : R2, z ≠ 0 → ‖fderiv ℝ localPlanarKernel z‖ ≤ C * (‖z‖ ^ 2)⁻¹)
    {X Y : R2 → R2} (hX : TorusAreaPreserving X) (hY : TorusAreaPreserving Y)
    (hh : 0 < h) (hh1 : h ≤ 1 / 4) (x y : R2)
    (hargs : ∀ᵐ b ∂μT, w b ≠ 0 → ‖((x + torusCenter) - X b) - ((y + torusCenter) - Y b)‖ ≤ h) :
    ‖periodicLocalMaterialVelocity w X x - periodicLocalMaterialVelocity w Y y‖ ≤
      5 * B * h + (8 * Real.pi * C * B * h) * Real.log (1 / (2 * h)) +
        (4 * C * h) * ∫ b in torusBox, ‖w b‖ := by
  have hzero1 := coupledNearProfile_zero_of_one_le (show 2 * h ≤ 1 by linarith)
  have hzero2 := coupledNearProfile_zero_of_one_le (show 3 * h ≤ 1 by linarith)
  have hzero3 := coupledAnnularProfile_zero_of_one_le h
  let N₁ (b : R2) := periodicCenteredSource (coupledNearProfile (2 * h)) ((x + torusCenter) - X b)
  let N₂ (b : R2) := periodicCenteredSource (coupledNearProfile (3 * h)) ((y + torusCenter) - Y b)
  let A (b : R2) := periodicCenteredSource (coupledAnnularProfile h) ((x + torusCenter) - X b)
  have hi₁ : Integrable N₁ μT := integrable_periodicCenteredSource_material (integrable_coupledNearProfile _) hzero1 hX x
  have hi₂ : Integrable N₂ μT := integrable_periodicCenteredSource_material (integrable_coupledNearProfile _) hzero2 hY y
  have hi₃ : Integrable A μT := integrable_periodicCenteredSource_material (integrable_coupledAnnularProfile hh) hzero3 hX x
  have hn₁ (b : R2) : 0 ≤ N₁ b := periodicCenteredSource_nonneg hzero1 (fun _ => truncInvNorm_nonneg _ _) _
  have hn₂ (b : R2) : 0 ≤ N₂ b := periodicCenteredSource_nonneg hzero2 (fun _ => truncInvNorm_nonneg _ _) _
  have hn₃ (b : R2) : 0 ≤ A b := periodicCenteredSource_nonneg hzero3 (fun _ => annKernel_nonneg _ _) _
  let G (b : R2) := B / (2 * Real.pi) * N₁ b + B / (2 * Real.pi) * N₂ b +
    (4 * C * h * B) * A b + (4 * C * h) * ‖w b‖
  have i1 := hi₁.const_mul (B / (2 * Real.pi))
  have i2 := hi₂.const_mul (B / (2 * Real.pi))
  have i3 := hi₃.const_mul (4 * C * h * B)
  have i4 := hw.norm.const_mul (4 * C * h)
  have i12 : Integrable (fun b => B / (2 * Real.pi) * N₁ b + B / (2 * Real.pi) * N₂ b) μT := i1.add i2
  have i123 : Integrable (fun b => B / (2 * Real.pi) * N₁ b + B / (2 * Real.pi) * N₂ b +
      (4 * C * h * B) * A b) μT := i12.add i3
  have hGi : Integrable G μT := i123.add i4
  have hbound : ∀ᵐ b ∂μT,
      ‖w b • (periodicLocalKernel ((x + torusCenter) - X b) - periodicLocalKernel ((y + torusCenter) - Y b))‖ ≤ G b := by
    filter_upwards [hB, hargs] with b hb harg
    have hN1 := hn₁ b
    have hN2 := hn₂ b
    have hAn := hn₃ b
    by_cases hw0 : w b = 0
    · simp only [hw0, zero_smul, norm_zero]
      dsimp only [G]
      positivity
    · rw [norm_smul]
      have hk := periodic_local_kernel_diff_split_bounded hC hderiv hh hh1 (harg hw0)
      have hP : 0 ≤ (N₁ b + N₂ b) / (2 * Real.pi) + (4 * C * h) * A b := by positivity
      calc
        _ ≤ ‖w b‖ * ((N₁ b + N₂ b) / (2 * Real.pi) + (4 * C * h) * A b + 4 * C * h) :=
          mul_le_mul_of_nonneg_left hk (norm_nonneg _)
        _ ≤ B * ((N₁ b + N₂ b) / (2 * Real.pi) + (4 * C * h) * A b) + (4 * C * h) * ‖w b‖ := by
          nlinarith [mul_le_mul_of_nonneg_right hb hP]
        _ = _ := by dsimp only [G]; ring
  have e1 : (∫ b in torusBox, N₁ b) = 2 * Real.pi * (2 * h) :=
    (integral_periodicCenteredSource_material (integrable_coupledNearProfile _) hzero1 hX x).trans
      (integral_coupledNearProfile (by positivity))
  have e2 : (∫ b in torusBox, N₂ b) = 2 * Real.pi * (3 * h) :=
    (integral_periodicCenteredSource_material (integrable_coupledNearProfile _) hzero2 hY y).trans
      (integral_coupledNearProfile (by positivity))
  have e3 : (∫ b in torusBox, A b) = 2 * Real.pi * Real.log (1 / (2 * h)) :=
    (integral_periodicCenteredSource_material (integrable_coupledAnnularProfile hh) hzero3 hX x).trans
      (integral_coupledAnnularProfile hh (by linarith))
  have hIG : (∫ b in torusBox, G b) =
      5 * B * h + (8 * Real.pi * C * B * h) * Real.log (1 / (2 * h)) +
        (4 * C * h) * ∫ b in torusBox, ‖w b‖ := by
    dsimp only [G]
    rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, e1, e2, e3]
    field_simp
    ring
  unfold periodicLocalMaterialVelocity
  rw [← integral_sub (integrable_periodicLocalMaterial_integrand hw hB hX x)
    (integrable_periodicLocalMaterial_integrand hw hB hY y)]
  have he : (fun b => w b • periodicLocalKernel ((x + torusCenter) - X b) -
      w b • periodicLocalKernel ((y + torusCenter) - Y b)) =
      (fun b => w b • (periodicLocalKernel ((x + torusCenter) - X b) -
        periodicLocalKernel ((y + torusCenter) - Y b))) := funext (fun b => (smul_sub _ _ _).symm)
  rw [he]
  exact (norm_integral_le_of_norm_le hGi hbound).trans_eq hIG

end Euler2D

end
