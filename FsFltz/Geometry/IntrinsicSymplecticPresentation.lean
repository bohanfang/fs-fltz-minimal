import FsFltz.Geometry.IntrinsicExtensionSymplectic
import FsFltz.Geometry.IntrinsicScalarExtension

/-!
# A native symplectic presentation produced by one intrinsic collar

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The source-derived collar constructs one compact domain, its
smooth primitive, and a native diffeomorphism from the original manifold onto
that same domain. The literal ambient inclusion agrees with this
correspondence, and preserves the entire primitive and actual exterior
derivative. Symplecticity holds on the literal compact carrier. Every locally
extendible source scalar extends smoothly on this same presentation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- A single collar constructed from the native primitive and its outwardness
produces a native diffeomorphism onto the same symplectic compact-domain
presentation. The correspondence, primitive extension, and full actual
exterior pullback, and universal scalar extensions are all conclusions, with
no additional source assumption. The same domain is selected before scalars. -/
theorem exists_compactDomain_with_native_symplectic_and_scalar_extensions
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hout : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧
        (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector α (exteriorDerivative α) x.val))) :
    ∃ (D : CompactDomain (k + 1)) (i : M → D.extension.Point) (lam : D.extension.Form 1)
      (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞),
      (∀ x, (e x).val = i x) ∧
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i ∧
      Topology.IsClosedEmbedding i ∧
      (∀ x, Function.Bijective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) ∧
      range i = D.carrier ∧
      frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M ∧
      D.extension.IsSmoothForm lam ∧
      (fun x => (lam (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α ∧
      (fun x => (D.extension.exteriorDerivative lam (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = exteriorDerivative α ∧
      D.extension.IsSymplecticOn (D.extension.exteriorDerivative lam) D.carrier ∧
      ∀ f : M → ℝ, IsLocallyExtendibleScalar (k := k) f →
        ∃ g : D.extension.Point → ℝ,
          ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ g ∧ ∀ x, g (i x) = f x := by
  obtain ⟨D, i, lam, e, he, hi, hemb, hbij, hrange, hfrontier, hlam, hpull, hscalar⟩ :=
    exists_compactDomain_with_native_primitive_and_scalar_extensions α hα hnd hout
  have hd := exteriorDerivative_pullback_from_boundaryless D.extension i hi lam hlam
  rw [hpull] at hd
  refine ⟨D, i, lam, e, he, hi, hemb, hbij, hrange, hfrontier,
    hlam, hpull, hd.symm, ?_, hscalar⟩
  apply (D.extension.isSymplecticOn_exteriorDerivative_iff lam hlam D.carrier).mpr
  intro z hz
  rw [← hrange] at hz
  obtain ⟨x, rfl⟩ := hz
  exact nondegenerate_exteriorDerivative_of_native_pullback D.extension i hi lam hlam α
    hpull x (hbij x) (hnd x)

/-- The original native symplectic presentation is a projection of the same
source-derived presentation that also extends every source-smooth scalar. -/
theorem exists_compactDomain_with_native_symplectic_presentation
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hout : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧
        (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector α (exteriorDerivative α) x.val))) :
    ∃ (D : CompactDomain (k + 1)) (i : M → D.extension.Point) (lam : D.extension.Form 1)
      (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D.Point ∞),
      (∀ x, (e x).val = i x) ∧
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i ∧
      Topology.IsClosedEmbedding i ∧
      (∀ x, Function.Bijective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) ∧
      range i = D.carrier ∧
      frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M ∧
      D.extension.IsSmoothForm lam ∧
      (fun x => (lam (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α ∧
      (fun x => (D.extension.exteriorDerivative lam (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = exteriorDerivative α ∧
      D.extension.IsSymplecticOn (D.extension.exteriorDerivative lam) D.carrier := by
  obtain ⟨D, i, lam, e, he, hi, hemb, hbij, hrange, hfrontier, hlam, hpull, hd, hs, _⟩ :=
    exists_compactDomain_with_native_symplectic_and_scalar_extensions α hα hnd hout
  exact ⟨D, i, lam, e, he, hi, hemb, hbij, hrange, hfrontier, hlam, hpull, hd, hs⟩

end FsFltz.Geometry.IntrinsicLiouville
