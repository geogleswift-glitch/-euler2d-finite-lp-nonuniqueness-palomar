module

public import Mathlib
public import RequestProject.Euler.AreaChart

/-!
# Material-phase operators (Lemmas `ib:lem:chart-equivariance` and `ib:lem:phase`)

Two-interface contours are pairs `z = (z₁, z₂)` of loops `ℝ → ℂ`. In normalized single-cell
time the paper puts
`S_τ(z₁, z₂) = (e^{iτ/2} z₁, z₂)` (`valueRot`),
`T_τ(z₁, z₂) = (z₁(· + τ/2), z₂)` (`paramShift`) and `C_τ = T_τ⁻¹ S_τ` (`phaseC`).

* `chart_componentwise_equivariant` (Lemma `ib:lem:chart-equivariance`): the area chart
  commutes with each operator `z_i ↦ e^{iφ_i} z_i(· − φ_i)`.
* `phaseC_eq`: `C_τ(z₁, z₂) = (G_{τ/2} z₁, z₂)`, hence `C_τ` fixes the reference pair
  (`phaseC_refCircle`) and preserves both areas (`loopArea_phaseC`).
* `phase_conjugacy`: for any flow map `Φ` commuting with every `T_τ`,
  `S_{−τ} Φ S_τ = C_τ⁻¹ Φ C_τ`; with `S_{τ+4π} = S_τ` (`valueRot_periodic`).
* `restored_contour`: `S_τ (C_τ⁻¹ v) = T_τ v`.

That the contour flow commutes with parameter shifts (a change of variables in the contour
integrals) is taken as a hypothesis.
-/

@[expose] public section

open Complex Real

namespace Euler2D

/-- A pair of loops. -/
abbrev LoopPair := (ℝ → ℂ) × (ℝ → ℂ)

/-- `S_τ(z₁, z₂) = (e^{iτ/2} z₁, z₂)`. -/
noncomputable def valueRot (τ : ℝ) (z : LoopPair) : LoopPair :=
  (fun θ => exp ((τ / 2 : ℝ) * I) * z.1 θ, z.2)

/-- `T_τ(z₁, z₂) = (z₁(· + τ/2), z₂)`. -/
noncomputable def paramShift (τ : ℝ) (z : LoopPair) : LoopPair := (fun θ => z.1 (θ + τ / 2), z.2)

/-- `C_τ = T_τ⁻¹ S_τ = T_{−τ} S_τ`. -/
noncomputable def phaseC (τ : ℝ) (z : LoopPair) : LoopPair := paramShift (-τ) (valueRot τ z)

/-- `C_τ⁻¹ = S_{−τ} T_τ`. -/
noncomputable def phaseCinv (τ : ℝ) (z : LoopPair) : LoopPair := valueRot (-τ) (paramShift τ z)

lemma valueRot_add (a b : ℝ) (z : LoopPair) : valueRot a (valueRot b z) = valueRot (a + b) z := by
  simp only [valueRot, ← mul_assoc, ← Complex.exp_add]
  congr 4
  push_cast; ring_nf

lemma valueRot_zero (z : LoopPair) : valueRot 0 z = z := by
  simp [valueRot]

lemma paramShift_add (a b : ℝ) (z : LoopPair) :
    paramShift a (paramShift b z) = paramShift (a + b) z := by
  simp only [paramShift]
  congr 2
  funext θ; ring_nf

lemma paramShift_zero (z : LoopPair) : paramShift 0 z = z := by
  simp [paramShift]

lemma valueRot_paramShift (a b : ℝ) (z : LoopPair) :
    valueRot a (paramShift b z) = paramShift b (valueRot a z) := rfl

lemma phaseCinv_phaseC (τ : ℝ) (z : LoopPair) : phaseCinv τ (phaseC τ z) = z := by
  simp only [phaseCinv, phaseC, paramShift_add, add_neg_cancel, paramShift_zero, valueRot_add,
    neg_add_cancel, valueRot_zero]

lemma phaseC_phaseCinv (τ : ℝ) (z : LoopPair) : phaseC τ (phaseCinv τ z) = z := by
  simp only [phaseCinv, phaseC, valueRot_add, add_neg_cancel, valueRot_zero, valueRot_paramShift,
    paramShift_add, neg_add_cancel, paramShift_zero]

/-- `S_{τ+4π} = S_τ`. -/
lemma valueRot_periodic (τ : ℝ) (z : LoopPair) : valueRot (τ + 4 * π) z = valueRot τ z := by
  simp only [valueRot]
  congr 2
  funext θ
  rw [show (((τ + 4 * π) / 2 : ℝ) : ℂ) * I = ((τ / 2 : ℝ) : ℂ) * I + 2 * π * I by
    push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- `C_τ(z₁, z₂) = (G_{τ/2} z₁, z₂)`. -/
lemma phaseC_eq (τ : ℝ) (z : LoopPair) : phaseC τ z = (rotShift (τ / 2) z.1, z.2) := by
  simp only [phaseC, paramShift, valueRot]
  congr 2
  funext θ
  congr 2; ring_nf

/-- `C_τ` fixes the reference pair `z⁰ = (d₁ e^{iθ}, d₂ e^{iθ})`. -/
theorem phaseC_refCircle (τ d₁ d₂ : ℝ) :
    phaseC τ (refCircle d₁, refCircle d₂) = (refCircle d₁, refCircle d₂) := by
  rw [phaseC_eq, rotShift_refCircle]

/-- `C_τ` preserves both enclosed areas. -/
theorem loopArea_phaseC (τ : ℝ) {z : LoopPair} (h1 : ContDiff ℝ 1 z.1)
    (hp1 : Function.Periodic z.1 (2 * π)) :
    loopArea (phaseC τ z).1 = loopArea z.1 ∧ loopArea (phaseC τ z).2 = loopArea z.2 := by
  rw [phaseC_eq]
  exact ⟨loopArea_rotShift _ h1 hp1, rfl⟩

/-- **Lemma `ib:lem:chart-equivariance`.** The area chart, applied componentwise with radii
`(d₁, d₂)`, commutes with `z_i ↦ e^{iφ_i} z_i(· − φ_i)` for fixed `φ₁, φ₂`. -/
theorem chart_componentwise_equivariant (d₁ d₂ φ₁ φ₂ : ℝ) {v : LoopPair}
    (h1 : ContDiff ℝ 1 v.1) (hp1 : Function.Periodic v.1 (2 * π))
    (h2 : ContDiff ℝ 1 v.2) (hp2 : Function.Periodic v.2 (2 * π)) :
    (areaChart d₁ (rotShift φ₁ v.1), areaChart d₂ (rotShift φ₂ v.2)) =
      (rotShift φ₁ (areaChart d₁ v.1), rotShift φ₂ (areaChart d₂ v.2)) := by
  rw [areaChart_equivariant d₁ φ₁ h1 hp1, areaChart_equivariant d₂ φ₂ h2 hp2]

/-- **Phase conjugacy** (`ib:phase-conjugacy`): if the flow map `Φ` commutes with all
parameter shifts, then `S_{−τ} Φ S_τ = C_τ⁻¹ Φ C_τ`. -/
theorem phase_conjugacy (Φ : LoopPair → LoopPair)
    (hcomm : ∀ τ z, Φ (paramShift τ z) = paramShift τ (Φ z)) (τ : ℝ) (z : LoopPair) :
    valueRot (-τ) (Φ (valueRot τ z)) = phaseCinv τ (Φ (phaseC τ z)) := by
  simp only [phaseCinv, phaseC, hcomm, paramShift_add, add_neg_cancel, paramShift_zero]

/-- The restored contour: `S_τ (C_τ⁻¹ v) = T_τ v`. -/
theorem restored_contour (τ : ℝ) (v : LoopPair) : valueRot τ (phaseCinv τ v) = paramShift τ v := by
  simp only [phaseCinv, valueRot_add, add_neg_cancel, valueRot_zero]

end Euler2D
