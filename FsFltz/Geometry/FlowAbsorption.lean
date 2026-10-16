import FsFltz.Geometry.FlowBridge
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Finite negative-time absorption from a proper exhaustion

Source: `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 813–818,
and `lem:absorption`, lines 444–468. The compact-annulus differential
inequality proves finite absorption; no completion marking is assumed.
The consumer is the original ambient and regular-fiber inclusion marking
required by `geoemtric-part-fsf.tex`, `g:initial`, lines 374–384.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry

/-- A continuous positive orbit derivative on each compact exhaustion band
forces entry in finite negative time. Positivity includes the boundary
level, so the lower bound on the closed annulus is strictly positive. -/
theorem exists_nonneg_time_flow_scalar_le
    {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) (ρ q : X → ℝ)
    (hρ : Continuous ρ) (hq : Continuous q)
    (hcompact : ∀ B : ℝ, IsCompact {x : X | ρ x ≤ B})
    (hderiv : ∀ x t, HasDerivAt (fun s => ρ (F s x)) (q (F t x)) t)
    (A : ℝ) (hpos : ∀ x, A ≤ ρ x → 0 < q x) (x : X) :
    ∃ T : ℝ, 0 ≤ T ∧ ρ (F (-T) x) ≤ A := by
  by_contra habsorb
  have hout : ∀ t : ℝ, t ≤ 0 → A < ρ (F t x) := by
    intro t ht
    have hn : ¬ ρ (F (-(-t)) x) ≤ A := by
      intro h
      exact habsorb ⟨-t, neg_nonneg.mpr ht, h⟩
    simpa only [neg_neg] using lt_of_not_ge hn
  let f : ℝ → ℝ := fun t => ρ (F t x)
  have hf : Differentiable ℝ f := fun t => (hderiv x t).differentiableAt
  have hmono : MonotoneOn f (Iic 0) :=
    monotoneOn_of_deriv_nonneg (convex_Iic 0) hf.continuous.continuousOn
      hf.differentiableOn fun t ht => by
        rw [(hderiv x t).deriv]
        exact (hpos _ (le_of_lt (hout t (mem_Iic.mp (interior_subset ht))))).le
  have hupper : ∀ t : ℝ, t ≤ 0 → ρ (F t x) ≤ ρ x := by
    intro t ht
    simpa only [f, Flow.map_zero_apply] using hmono ht (by simp) ht
  let band : Set X := {y | ρ y ≤ ρ x} ∩ {y | A ≤ ρ y}
  have hband : IsCompact band :=
    (hcompact (ρ x)).inter_right (isClosed_le continuous_const hρ)
  have hxband : x ∈ band := by
    change ρ x ≤ ρ x ∧ A ≤ ρ x
    exact ⟨le_rfl, by simpa only [Flow.map_zero_apply] using (hout 0 le_rfl).le⟩
  obtain ⟨y, hy, hmin⟩ := hband.exists_isMinOn ⟨x, hxband⟩ hq.continuousOn
  have hc : 0 < q y := hpos y hy.2
  have hbound : ∀ t ∈ interior (Iic (0 : ℝ)), q y ≤ deriv f t := by
    intro t ht
    rw [(hderiv x t).deriv]
    exact hmin ⟨hupper t (mem_Iic.mp (interior_subset ht)),
      (hout t (mem_Iic.mp (interior_subset ht))).le⟩
  let T : ℝ := (ρ x - A + 1) / q y
  have hT : 0 < T := div_pos (by
    have hA : A ≤ ρ x := hxband.2
    linarith) hc
  have hslope := (convex_Iic (0 : ℝ)).mul_sub_le_image_sub_of_le_deriv
    hf.continuous.continuousOn hf.differentiableOn hbound
    (-T) (by simpa only [mem_Iic] using (neg_neg_of_pos hT).le)
    0 (by simp) (by linarith)
  have hmul : q y * T = ρ x - A + 1 := by
    dsimp only [T]
    exact mul_div_cancel₀ _ (ne_of_gt hc)
  have houtside := hout (-T) (by linarith)
  simp only [f, Flow.map_zero_apply, sub_neg_eq_add, zero_add] at hslope
  rw [hmul] at hslope
  linarith

namespace SmoothManifold

/-- The exhaustion derivative along a smooth native vector field is
continuous. This follows from the tangent map and the native section. -/
theorem continuous_scalarDerivative_vectorField {d : ℕ} {M : SmoothManifold d}
    {Z : (x : M.Point) → M.Tangent x} (hZ : M.IsSmoothVectorField Z)
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ) :
    Continuous (fun x => M.scalarDerivative ρ x (Z x)) := by
  exact ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).continuous.comp
    ((hρ.continuous_tangentMap (by simp)).comp hZ.contMDiff_section.continuous)).snd

end SmoothManifold

namespace CompleteLiouvilleFlow

set_option backward.isDefEq.respectTransparency false in
/-- The orbit derivative of a smooth exhaustion is its actual differential
on the field defining this very complete flow. -/
theorem hasDerivAt_scalar_orbit {d : ℕ} {M : SmoothManifold d}
    {Z : (x : M.Point) → M.Tangent x} (F : CompleteLiouvilleFlow M Z)
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    (x : M.Point) (t : ℝ) :
    HasDerivAt (fun s => ρ (F.flow s x))
      (M.scalarDerivative ρ (F.flow t x) (Z (F.flow t x))) t := by
  have h := (hasMFDerivAt_iff_hasFDerivAt.mp
    ((hρ.mdifferentiableAt (by simp)).hasMFDerivAt.comp t
      (F.isMIntegralCurve x t))).hasDerivAt
  apply h.congr_deriv
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ (F.flow t x)
    ((1 : ℝ) • Z (F.flow t x)) = _
  rw [one_smul]
  rfl

/-- Every point enters a proper exhaustion sublevel in finite negative
time when its actual field derivative is positive on and above the level.
This applies to both the original ambient field and intrinsic fiber field
in `lem:originalends`, once their completeness and end estimates are proved.
It constructs no completion marking by itself. -/
theorem exists_nonneg_time_scalar_le {d : ℕ} {M : SmoothManifold d}
    {Z : (x : M.Point) → M.Tangent x} (F : CompleteLiouvilleFlow M Z)
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    (hZ : M.IsSmoothVectorField Z)
    (hcompact : ∀ B : ℝ, IsCompact {x : M.Point | ρ x ≤ B})
    (A : ℝ) (hpos : ∀ x, A ≤ ρ x → 0 < M.scalarDerivative ρ x (Z x))
    (x : M.Point) : ∃ T : ℝ, 0 ≤ T ∧ ρ (F.flow (-T) x) ≤ A :=
  exists_nonneg_time_flow_scalar_le F.flow ρ
    (fun y => M.scalarDerivative ρ y (Z y)) hρ.continuous
    (SmoothManifold.continuous_scalarDerivative_vectorField hZ ρ hρ) hcompact
    (F.hasDerivAt_scalar_orbit ρ hρ) A hpos x

end CompleteLiouvilleFlow

end FsFltz.Geometry
