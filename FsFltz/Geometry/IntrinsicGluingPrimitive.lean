import FsFltz.Geometry.IntrinsicCylinderTime
import FsFltz.Geometry.IntrinsicBoundaryForm
import FsFltz.Geometry.IntrinsicFormPullback
import FsFltz.Geometry.IntrinsicBoundaryCollarPrimitive
import FsFltz.Geometry.BoundaryNondegeneracy

/-!
# Actual primitive pieces for the boundaryless native collar gluing

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The interior piece is the actual native pullback. The
two-sided cylinder piece is `exp(-t)` times the actual boundary pullback.
Both smoothness statements are proved from the original locally extendible
primitive; no smooth cylinder or interior primitive is supplied as input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCollarGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]

/-- The original primitive on the constructed boundaryless native interior. -/
def interiorPrimitive (α : IntrinsicLiouville.Form k M 1) :
    (IntrinsicInterior.smoothManifold k M).Form 1 :=
  IntrinsicLiouville.pullbackForm (IntrinsicInterior.smoothManifold k M) Subtype.val α

theorem isSmoothForm_interiorPrimitive (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α) :
    (IntrinsicInterior.smoothManifold k M).IsSmoothForm (interiorPrimitive α) :=
  IntrinsicLiouville.isSmoothForm_pullbackForm_one
    (IntrinsicInterior.smoothManifold k M) Subtype.val IntrinsicInterior.contMDiff_val α hα

/-- Projection of the actual recharted cylinder to the literal intrinsic boundary. -/
def boundaryProjection {δ : ℝ} (p : Band δ (IntrinsicBoundary.Point k M)) :
    IntrinsicBoundary.Point k M := p.val.2

omit [T2Space M] [SecondCountableTopology M] in
theorem contMDiff_boundaryProjection (δ : ℝ) :
    letI := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
    ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) ∞
      (boundaryProjection : Band δ (IntrinsicBoundary.Point k M) → _) := by
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
  have h := (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, Model k)) (n := ∞)).comp
    (contMDiff_band_val (k := k) (B := IntrinsicBoundary.Point k M) δ)
  exact h

/-- The prescribed smooth cylinder primitive on both sides of the seam. -/
def cylinderPrimitive (δ : ℝ) (α : IntrinsicLiouville.Form k M 1) :
    (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).Form 1 :=
  fun p => Real.exp (-p.val.1) •
    ((bandManifold δ (IntrinsicBoundary.smoothManifold k M)).pullback
      (IntrinsicBoundary.smoothManifold k M) boundaryProjection
      (IntrinsicBoundary.restrictForm α) p)

/-- Cylinder smoothness follows from actual boundary restriction, smooth
projection and smooth exponential multiplication in the final cylinder model. -/
theorem isSmoothForm_cylinderPrimitive (δ : ℝ) (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α) :
    (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).IsSmoothForm
      (cylinderPrimitive δ α) := by
  let N := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
  have hp : N.IsSmoothForm
      (N.pullback (IntrinsicBoundary.smoothManifold k M) boundaryProjection
        (IntrinsicBoundary.restrictForm α)) :=
    N.isSmoothForm_pullback_one (IntrinsicBoundary.smoothManifold k M)
      ⟨boundaryProjection, contMDiff_boundaryProjection δ⟩ (IntrinsicBoundary.restrictForm α)
      (IntrinsicBoundary.isSmoothForm_restrictForm α hα)
  have ht : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : N.Point => p.val.1) :=
    contMDiff_bandTime (k := k) (B := IntrinsicBoundary.Point k M) δ
  exact hp.function_smul (Real.contDiff_exp.contMDiff.comp ht.neg)

/-- The cylinder primitive uses the actual differential of the boundary
projection and of the original boundary inclusion on every tangent vector. -/
theorem cylinderPrimitive_eval (δ : ℝ) (α : IntrinsicLiouville.Form k M 1)
    (p : Band δ (IntrinsicBoundary.Point k M))
    (w : Model (k + 1)) :
    letI := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
    cylinderPrimitive δ α p (fun _ => w) = Real.exp (-p.val.1) *
      α p.val.2.val (fun _ =>
        mfderiv 𝓘(ℝ, Model k) (𝓡∂ (k + 1))
          (Subtype.val : IntrinsicBoundary.Point k M → M) p.val.2
          (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k)
            boundaryProjection p w)) := by
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
  rfl

/-- On the actual positive collar overlap, the pullback of the original
primitive equals the constructed smooth cylinder primitive on every tangent.
Compatibility is derived from the same collar's Liouville equation and ODE. -/
theorem pullbackForm_collar_eq_cylinderPrimitive
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hZ : IntrinsicLiouville.Contraction α (IntrinsicLiouville.exteriorDerivative α) Z)
    (C : ℝ × IntrinsicBoundary.Point k M → M) {δ : ℝ} (hδ : 0 < δ)
    (hC : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
      (Ico 0 δ ×ˢ univ))
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y)) (fun x => -Z x) (Ico 0 δ))
    (hzero : ∀ y, C (0, y) = y.val)
    (p : Band δ (IntrinsicBoundary.Point k M)) (hp : 0 < p.val.1) :
    IntrinsicLiouville.pullbackForm
      (bandManifold δ (IntrinsicBoundary.smoothManifold k M)) (C ∘ Subtype.val) α p =
        cylinderPrimitive δ α p := by
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
  have hnhd : Ico 0 δ ×ˢ (univ : Set (IntrinsicBoundary.Point k M)) ∈ 𝓝 p.val := by
    apply mem_of_superset ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      (show p.val ∈ Ioo 0 δ ×ˢ (univ : Set (IntrinsicBoundary.Point k M)) from
        ⟨⟨hp, p.property.1.2⟩, mem_univ _⟩))
    intro q hq
    exact ⟨⟨hq.1.1.le, hq.1.2⟩, hq.2⟩
  have hval := contMDiff_band_val (k := k) (B := IntrinsicBoundary.Point k M) δ
  have hchain := mfderiv_comp
    (I := 𝓘(ℝ, Model (k + 1))) (I' := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
    (I'' := 𝓡∂ (k + 1))
    (f := (Subtype.val : Band δ (IntrinsicBoundary.Point k M) → _)) (g := C) p
    ((hC.contMDiffAt hnhd).mdifferentiableAt (by simp))
    (hval.mdifferentiableAt (by simp))
  have hproj := mfderiv_comp
    (I := 𝓘(ℝ, Model (k + 1))) (I' := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
    (I'' := 𝓘(ℝ, Model k))
    (f := (Subtype.val : Band δ (IntrinsicBoundary.Point k M) → _))
    (g := (Prod.snd : ℝ × IntrinsicBoundary.Point k M → _)) p
    ((contMDiff_snd (n := ∞)).mdifferentiableAt (by simp)) (hval.mdifferentiableAt (by simp))
  rw [mfderiv_snd] at hproj
  ext vs
  have hvs : vs = fun _ => vs 0 := by funext i; rw [Fin.eq_zero i]
  rw [hvs, cylinderPrimitive_eval]
  unfold IntrinsicLiouville.pullbackForm
  change α (C p.val) (fun _ => mfderiv 𝓘(ℝ, Model (k + 1)) (𝓡∂ (k + 1))
    (C ∘ Subtype.val) p (vs 0)) = _
  rw [hchain]
  let v := mfderiv 𝓘(ℝ, Model (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
    (Subtype.val : Band δ (IntrinsicBoundary.Point k M) → _) p (vs 0)
  have hfull := IntrinsicLiouville.inward_boundary_pullbackWithin_eq_exp_mul_of_liouville
    α hα Z hZ C hδ hC hode hzero ⟨hp.le, p.property.1.2⟩ p.val.2 v.1 v.2
  rw [mfderivWithin_of_mem_nhds hnhd] at hfull
  change α (C p.val) (fun _ => mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
    (𝓡∂ (k + 1)) C p.val v) = _ at hfull
  rw [show mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) boundaryProjection p =
      (ContinuousLinearMap.snd ℝ ℝ (Model k)).comp
        (mfderiv 𝓘(ℝ, Model (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
          (Subtype.val : Band δ (IntrinsicBoundary.Point k M) → _) p) from hproj]
  exact hfull

end FsFltz.Geometry.IntrinsicCollarGluing
