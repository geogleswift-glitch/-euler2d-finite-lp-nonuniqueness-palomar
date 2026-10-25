module

public import RequestProject.Euler.ContourLittleShiftContinuity
public import RequestProject.Euler.TorusForcedFinitePhaseFlow
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Algebra.Field.Periodic

/-! Closed phase tubes in the original little Banach space. Compactness
is used only for the finitely many phase parameters, never for a bounded
ball of contour functions. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) phaseTubeLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) phaseTubeLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) phaseTubeC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

theorem periodic_contourParameterShiftLittle {γ : ℝ≥0} (Z : LittleContourSpace γ) :
    Function.Periodic (fun b : ℝ => contourParameterShiftLittleCLM γ b Z) (2 * Real.pi) := by
  intro b
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change LittleContourSpace.lift γ (contourParameterShiftLittleCLM γ (b + 2 * Real.pi) Z) θ =
    LittleContourSpace.lift γ (contourParameterShiftLittleCLM γ b Z) θ
  rw [lift_contourParameterShiftLittleCLM, lift_contourParameterShiftLittleCLM,
    show θ + (b + 2 * Real.pi) = (θ + b) + 2 * Real.pi by ring]
  exact LittleContourSpace.periodic_lift Z (θ + b)

theorem norm_parameterShift_sub_reference {γ : ℝ≥0} (b : ℝ)
    (Z Ref : LittleContourSpace γ) :
    ‖contourParameterShiftLittleCLM γ b Z - Ref‖ =
      ‖Z - contourParameterShiftLittleCLM γ (-b) Ref‖ := by
  have hh := norm_contourParameterShiftLittleCLM (-b)
    (contourParameterShiftLittleCLM γ b Z - Ref)
  rw [map_sub, contourParameterShiftLittleCLM_add, neg_add_cancel,
    contourParameterShiftLittleCLM_zero] at hh
  exact hh.symm

def closedPhaseTube {γ : ℝ≥0} {ι : Type*}
    (Ref : ι → LittleContourSpace γ) (ε : ι → ℝ) : Set (ι → LittleContourSpace γ) :=
  {Z | ∃ b : ι → ℝ, ∀ i, ‖contourParameterShiftLittleCLM γ (b i) (Z i) - Ref i‖ ≤ ε i}

theorem isClosed_closedPhaseTube {γ : ℝ≥0} (hγ1 : γ ≤ 1) {ι : Type*} [Fintype ι]
    (Ref : ι → LittleContourSpace γ) (ε : ι → ℝ) : IsClosed (closedPhaseTube Ref ε) := by
  classical
  let B := ι → Icc (0 : ℝ) (2 * Real.pi)
  let R : Set ((ι → LittleContourSpace γ) × B) :=
    {p | ∀ i, ‖p.1 i - contourParameterShiftLittleCLM γ (p.2 i) (Ref i)‖ ≤ ε i}
  have hR : IsClosed R := by
    have hi (i : ι) : IsClosed {p : (ι → LittleContourSpace γ) × B |
        ‖p.1 i - contourParameterShiftLittleCLM γ (p.2 i) (Ref i)‖ ≤ ε i} :=
      isClosed_le (((continuous_apply i).comp continuous_fst).sub
        ((continuous_contourParameterShiftLittleCLM hγ1 (Ref i)).comp
          (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)))).norm continuous_const
    simpa only [R, setOf_forall] using isClosed_iInter hi
  have he : closedPhaseTube Ref ε = Prod.fst '' R := by
    ext Z
    constructor
    · rintro ⟨b, hb⟩
      have hex (i : ι) := (periodic_contourParameterShiftLittle (Ref i)).exists_mem_Ico₀
        (by positivity : 0 < 2 * Real.pi) (-b i)
      choose c hc hec using hex
      let cB : B := fun i => ⟨c i, (hc i).1, (hc i).2.le⟩
      refine ⟨(Z, cB), ?_, rfl⟩
      intro i
      change ‖Z i - contourParameterShiftLittleCLM γ (c i) (Ref i)‖ ≤ ε i
      rw [← hec i, ← norm_parameterShift_sub_reference]
      exact hb i
    · rintro ⟨⟨W, c⟩, hc, rfl⟩
      refine ⟨fun i => -(c i : ℝ), ?_⟩
      intro i
      rw [norm_parameterShift_sub_reference, neg_neg]
      exact hc i
  rw [he]
  exact isClosedMap_fst_of_compactSpace R hR

theorem closedPhaseTube_mem_of_tendsto {γ : ℝ≥0} (hγ1 : γ ≤ 1) {ι : Type*} [Fintype ι]
    (Ref : ι → LittleContourSpace γ) (ε : ι → ℝ)
    {P : Type*} {l : Filter P} [NeBot l] {Z : P → ι → LittleContourSpace γ} {W : ι → LittleContourSpace γ}
    (hZ : Tendsto Z l (𝓝 W)) (hm : ∀ᶠ p in l, Z p ∈ closedPhaseTube Ref ε) :
    W ∈ closedPhaseTube Ref ε := (isClosed_closedPhaseTube hγ1 Ref ε).mem_of_tendsto hZ hm

theorem quarterPhase_of_closedPhaseTube {γ : ℝ≥0} {ι : Type*}
    (Ref : ι → LittleContourSpace γ) (r ε : ι → ℝ) (hε : ∀ i, ε i < r i / 4)
    {Z : ι → LittleContourSpace γ} (hZ : Z ∈ closedPhaseTube Ref ε) :
    IsQuarterPhaseLittleContourFamily (fun i => (Ref i).val) r Z := by
  obtain ⟨b, hb⟩ := hZ
  refine ⟨b, ?_⟩
  intro i
  exact (hb i).trans_lt (hε i)

end Euler2D

end
