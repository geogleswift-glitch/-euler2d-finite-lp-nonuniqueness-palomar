module

public import RequestProject.Euler.TorusPartialCanonicalForcing
public import RequestProject.Euler.BanachTimeDomainContinuation

/-! The validity domain of the actual partial equation explicitly
retains its literal physical lift. Consequently a trajectory of a
totalized auxiliary field outside that domain cannot be mistaken for
an actual material contour. Local starts and endpoint extensions
already supply both Banach and material derivatives, which verify
the validity condition by uniqueness of derivatives. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

def actualPartialPhaseField (q : R2 → ℝ) {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    (t : ℝ) (W : ι → LittleContourSpace γ) : ι → LittleContourSpace γ :=
  finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g W + S.actualPartialContourForcing q t W

def actualPartialPhaseDomain (q : R2 → ℝ) {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (a Hglob : ℝ)
    (t : ℝ) : Set (ι → LittleContourSpace γ) := {W |
  t ∈ Icc (0 : ℝ) Hglob ∧
    IsPhaseAdmissibleLittleContourFamily Z₀ r W ∧ ‖W‖ < a / 4 ∧
    IsQuarterPhaseLittleContourFamily Z₀ r W ∧
    ∀ i θ, LittleContourSpace.lift γ (S.actualPartialContourForcing q t W i) θ =
      S.physicalLabelComplexField q t (LittleContourSpace.lift γ (W i) θ)}

theorem hasDerivAt_lift_actualPartialPhaseField
    {q : R2 → ℝ} {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    {Z : ℝ → ι → LittleContourSpace γ} {t : ℝ}
    (hd : HasDerivAt Z (S.actualPartialPhaseField q hγ hγ1 Z₀ r hr href g t (Z t)) t)
    (hphase : IsPhaseAdmissibleLittleContourFamily Z₀ r (Z t)) (i : ι) (θ : ℝ) :
    HasDerivAt (fun u => LittleContourSpace.lift γ (Z u i) θ)
      (contourBoundaryField g (fun j => LittleContourSpace.lift γ (Z t j)) i θ +
        LittleContourSpace.lift γ (S.actualPartialContourForcing q t (Z t) i) θ) t := by
  have hh := ((LittleContourSpace.eval γ (θ : ContourCircle)).comp
    (ContinuousLinearMap.proj i)).hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun u => LittleContourSpace.lift γ (Z u i) θ)
    (LittleContourSpace.lift γ (finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g (Z t) i) θ +
      LittleContourSpace.lift γ (S.actualPartialContourForcing q t (Z t) i) θ) t at hh
  rwa [lift_finiteContourPhaseFieldTotal hγ hγ1 Z₀ r hr href g (Z t) hphase i θ] at hh

theorem actualPartialPhaseField_material_iff
    {q : R2 → ℝ} {γ : ℝ≥0} {ι : Type} [Fintype ι]
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i)) (g : ι → ℝ)
    {Z : ℝ → ι → LittleContourSpace γ} {t : ℝ}
    (hd : HasDerivAt Z (S.actualPartialPhaseField q hγ hγ1 Z₀ r hr href g t (Z t)) t)
    (hphase : IsPhaseAdmissibleLittleContourFamily Z₀ r (Z t)) :
    (∀ i θ, HasDerivAt (fun u => LittleContourSpace.lift γ (Z u i) θ)
      (contourBoundaryField g (fun j => LittleContourSpace.lift γ (Z t j)) i θ +
        S.physicalLabelComplexField q t (LittleContourSpace.lift γ (Z t i) θ)) t) ↔
    ∀ i θ, LittleContourSpace.lift γ (S.actualPartialContourForcing q t (Z t) i) θ =
      S.physicalLabelComplexField q t (LittleContourSpace.lift γ (Z t i) θ) := by
  constructor
  · intro hmat i θ
    exact add_left_cancel ((S.hasDerivAt_lift_actualPartialPhaseField hγ hγ1 Z₀ r hr href g hd hphase i θ).unique
      (hmat i θ))
  · intro hlift i θ
    have hh := S.hasDerivAt_lift_actualPartialPhaseField hγ hγ1 Z₀ r hr href g hd hphase i θ
    rwa [hlift i θ] at hh

end BoundedEulerParticleSystem
end Euler2D

end
