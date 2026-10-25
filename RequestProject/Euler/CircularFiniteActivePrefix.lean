module

public import RequestProject.Euler.CircularFinitePhaseLabelIdentification
public import RequestProject.Euler.CircularFiniteInnerLabelContinuity

/-! Restricting the interfaces to an active prefix retains the ancient
sample at the original cutoff. The complementary initial labels are
exactly the same inner source transported by the original Euler system. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D

def finiteCircularPrefixIndex {k N : ℕ} (hk : k ≤ N)
    (p : FiniteCircularIndex k) : FiniteCircularIndex N :=
  (⟨p.1.val, lt_of_lt_of_le p.1.isLt (Nat.add_le_add_right hk 1)⟩, p.2)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def finiteActivePlanarLabel (s A₀ b R ρ : ℝ) (N k : ℕ) (x : R2) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), P.finitePlanarLabel s A₀ b R ρ N j x

def finiteActiveInitialLabel (s A₀ b R ρ : ℝ) (N k : ℕ) (x : R2) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), P.finitePeriodicLabel s A₀ b R ρ N j x

theorem finiteActiveInitialLabel_add_inner {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {N k : ℕ} (hk : k ≤ N) (x : R2) :
    P.finiteActiveInitialLabel s A₀ b R ρ N k x +
      P.finiteInnerInitialLabel s A₀ b R ρ N k x =
        P.finiteInitialPeriodicDensity s A₀ b R ρ N x := by
  rw [P.finiteInitialPeriodicDensity_eq_sum_labels hs hR hRmax hρ hρ1 N x]
  exact Finset.sum_range_add_sum_Ico _ (Nat.add_le_add_right hk 1)

theorem finiteActiveInitialLabel_eq_on_box {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k : ℕ) {x : R2} (hx : x ∈ torusBox) :
    P.finiteActiveInitialLabel s A₀ b R ρ N k x =
      P.finiteActivePlanarLabel s A₀ b R ρ N k (x - torusCenter) := by
  apply Finset.sum_congr rfl
  intro j _
  exact periodicCenteredSource_eq_on_box
    (P.finitePlanarLabel_zero_of_one_le_norm hs hR hRmax hρ hρ1 N j) hx

theorem finiteCircularPrefix_initial_density_eq {s A₀ b R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) {N k : ℕ} (hk : k ≤ N) (x : ℂ) :
    phaseFiniteContourPatchVorticity (finiteCircularInterfaceStrength A₀ b)
      (fun p : FiniteCircularIndex k =>
        (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N
          (finiteCircularPrefixIndex hk p)).val) x =
        P.finiteActivePlanarLabel s A₀ b R ρ N k (complexPhysicalPlane x) := by
  unfold phaseFiniteContourPatchVorticity
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ j : Fin (k + 1),
        P.finitePlanarLabel s A₀ b R ρ N j (complexPhysicalPlane x) := by
      apply Finset.sum_congr rfl
      intro j _
      exact P.finiteCircularInitial_label_density_eq hR hρ N
        ⟨j.val, lt_of_lt_of_le j.isLt (Nat.add_le_add_right hk 1)⟩ x
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun j => P.finitePlanarLabel s A₀ b R ρ N j (complexPhysicalPlane x)) (k + 1)

theorem finiteCircularPrefix_initial_decomposition {s A₀ b R ρ q : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) {N k : ℕ} (hk : k ≤ N) :
    (fun x => torusExtension
      (fun y => P.finiteActivePlanarLabel s A₀ b R ρ N k (y - torusCenter)) x +
        P.finiteInnerInitialLabel s A₀ b R ρ N k x) =ᵐ[μT]
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N : R2 → ℝ) := by
  filter_upwards [torusExtension_ae
      (fun y => P.finiteActivePlanarLabel s A₀ b R ρ N k (y - torusCenter)),
    P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N,
    ae_restrict_mem measurableSet_torusBox] with x he hf hx
  rw [he, ← P.finiteActiveInitialLabel_eq_on_box hs hR hRmax hρ hρ1 N k hx,
    P.finiteActiveInitialLabel_add_inner hs hR hRmax hρ hρ1 hk x,
    P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hx]
  exact hf.symm

theorem finiteActiveInitialLabel_bounds {s A₀ b R ρ : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A₀) (hb : 0 < b) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N k : ℕ) :
    MemLp (P.finiteActiveInitialLabel s A₀ b R ρ N k) 2 μT ∧
      IsTorusPeriodic (P.finiteActiveInitialLabel s A₀ b R ρ N k) ∧
      ∀ x, ‖P.finiteActiveInitialLabel s A₀ b R ρ N k x‖ ≤
        ∑ j ∈ Finset.range (k + 1), finiteLabelAmplitudeBound * ampScale A₀ b j := by
  have hi : Integrable (P.finiteActiveInitialLabel s A₀ b R ρ N k) μT :=
    integrable_finset_sum _ fun j _ => (P.finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j).1
  have hbound (x : R2) : ‖P.finiteActiveInitialLabel s A₀ b R ρ N k x‖ ≤
      ∑ j ∈ Finset.range (k + 1), finiteLabelAmplitudeBound * ampScale A₀ b j := by
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
      (P.finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j).2.2.1 x)
  refine ⟨MemLp.of_bound hi.aestronglyMeasurable _ (ae_of_all _ hbound), ?_, hbound⟩
  intro x i
  apply Finset.sum_congr rfl
  intro j _
  exact (P.finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N j).2.1 x i

end CircularMaterialTransferProfile
end Euler2D

end
