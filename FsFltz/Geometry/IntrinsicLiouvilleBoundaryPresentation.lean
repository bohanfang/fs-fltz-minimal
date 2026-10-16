import FsFltz.Geometry.IntrinsicBoundaryPresentation
import FsFltz.Geometry.IntrinsicRibbonPair

/-!
# Native ambient and boundary presentations for witnessed pairs

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The native ambient Liouville data construct their actual compact
and boundary presentations through the same inclusion. Both native primitive
identities are preserved when passing to the constructed collar localization.
These are producers for positive-dimensional and zero-dimensional ribbons;
no completion onto a prescribed external ambient or comparison chain is asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

section AmbientPresentation

variable {a : ℕ} {A : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A]
  [IsManifold (𝓡∂ (a + 1)) ∞ A]

/-- Native ambient data construct their compact and boundary presentations
together, preserving the same inclusion and the actual boundary restriction. -/
theorem exists_liouvilleDomain_with_native_boundary_presentation
    (lam : Form a A 1) (hlam : IsLocallyExtendibleForm lam)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative lam) x)
    (hout : ∀ x : IntrinsicBoundary.Point a A,
      ∃ (rho : A → ℝ) (beta : Model (a + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector lam (exteriorDerivative lam) x.val))) :
    ∃ (D : LiouvilleDomain (a + 1)) (i : A → D.domain.extension.Point)
      (e : Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (a + 1)) A D.domain.Point ∞)
      (eB : (IntrinsicBoundary.smoothManifold a A).SmoothEquiv D.domain.boundary),
      (∀ x, (e x).val = i x) ∧
      ContMDiff (𝓡∂ (a + 1)) 𝓘(ℝ, Model (a + 1)) ∞ i ∧
      (∀ x, Function.Bijective (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (a + 1)) i x)) ∧
      range i = D.domain.carrier ∧
      (fun x => (D.liouville.primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (a + 1)) i x)) = lam ∧
      (∀ x, D.domain.boundaryInclusion.map (eB x) = i x.val) ∧
      (IntrinsicBoundary.smoothManifold a A).pullback D.domain.boundary eB
        (D.domain.boundaryForm D.liouville.primitive) = IntrinsicBoundary.restrictForm lam := by
  obtain ⟨D, i, e, he, hi, hemb, hdi, hrange, hfrontier, hpull, _, _, _, _, _⟩ :=
    exists_liouvilleDomain_with_native_presentation_and_scalar_extensions lam hlam hnd hout
  let eB := boundaryPresentationEquiv D.domain i hi hemb.injective (fun x => (hdi x).1) hfrontier
  exact ⟨D, i, e, eB, he, hi, hdi, hrange, hpull,
    boundaryPresentationEquiv_inclusion D.domain i hi hemb.injective (fun x => (hdi x).1) hfrontier,
    pullback_boundaryForm D.domain i hi hemb.injective (fun x => (hdi x).1) hfrontier
      lam D.liouville.primitive hpull⟩

omit [CompactSpace A] in
/-- Changing only the presentation dimension index preserves the original
native source atlas and all maps and primitive identities. -/
theorem native_boundary_presentation_dimension_eq {r : ℕ} [NeZero r]
    (hdim : a + 1 = r) (lam : Form a A 1)
    (h : ∃ (D : LiouvilleDomain (a + 1)) (i : A → D.domain.extension.Point)
      (e : Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (a + 1)) A D.domain.Point ∞)
      (eB : (IntrinsicBoundary.smoothManifold a A).SmoothEquiv D.domain.boundary),
      (∀ x, (e x).val = i x) ∧
      ContMDiff (𝓡∂ (a + 1)) 𝓘(ℝ, Model (a + 1)) ∞ i ∧
      (∀ x, Function.Bijective (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (a + 1)) i x)) ∧
      range i = D.domain.carrier ∧
      (fun x => (D.liouville.primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (a + 1)) i x)) = lam ∧
      (∀ x, D.domain.boundaryInclusion.map (eB x) = i x.val) ∧
      (IntrinsicBoundary.smoothManifold a A).pullback D.domain.boundary eB
        (D.domain.boundaryForm D.liouville.primitive) = IntrinsicBoundary.restrictForm lam) :
    ∃ (D : LiouvilleDomain r) (i : A → D.domain.extension.Point)
      (e : Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ r) A D.domain.Point ∞)
      (eB : (IntrinsicBoundary.smoothManifold a A).SmoothEquiv D.domain.boundary),
      (∀ x, (e x).val = i x) ∧
      ContMDiff (𝓡∂ (a + 1)) 𝓘(ℝ, Model r) ∞ i ∧
      (∀ x, Function.Bijective (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model r) i x)) ∧
      range i = D.domain.carrier ∧
      (fun x => (D.liouville.primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model r) i x)) = lam ∧
      (∀ x, D.domain.boundaryInclusion.map (eB x) = i x.val) ∧
      (IntrinsicBoundary.smoothManifold a A).pullback D.domain.boundary eB
        (D.domain.boundaryForm D.liouville.primitive) = IntrinsicBoundary.restrictForm lam := by
  subst r
  exact h

end AmbientPresentation

section LocalizedPrimitive

variable {a d : ℕ} [NeZero d] {A : Type} [TopologicalSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A]

omit [NeZero d] in
/-- The original inclusion of a collar localization has identity model
differential, because both maps are actual open-subset inclusions. -/
theorem mfderiv_originalInclusion (D : LiouvilleDomain d) (C : D.FlowCollar)
    (z : C.localizedDomain.domain.extension.Point) :
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.originalInclusion.map z =
      ContinuousLinearMap.id ℝ (Model d) := by
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
    (fun y : C.localizedDomain.domain.extension.Point => y.val.val) z = _
  erw [D.neighborhoodDomain.extension.mfderiv_comp_restrict_val D.domain.extension
    C.neighborhood z
    ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp)),
    D.domain.extension.mfderiv_restrict_val]
  rfl

/-- Passing to the constructed collar localization preserves every native
tangent direction of the original primitive through its compact diffeomorphism. -/
theorem native_primitive_localizedDomain (D : LiouvilleDomain d) (C : D.FlowCollar)
    (e : Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ d) A D.domain.Point ∞)
    (lam : Form a A 1)
    (hpull : ∀ x, (D.liouville.primitive (e x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model d) (fun y => (e y).val) x) = lam x) :
    ∀ x, (C.localizedDomain.liouville.primitive
      ((e.trans C.originalPointDiffeomorph.symm) x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model d)
          (fun y => ((e.trans C.originalPointDiffeomorph.symm) y).val) x) = lam x := by
  let eP := e.trans C.originalPointDiffeomorph.symm
  let iP : A → C.localizedDomain.domain.extension.Point := fun x => (eP x).val
  have hiP : ContMDiff (𝓡∂ (a + 1)) 𝓘(ℝ, Model d) ∞ iP :=
    C.localizedDomain.domain.contMDiff_subtype_val.comp eP.contMDiff
  have heP (x : A) : C.originalInclusion.map (iP x) = (e x).val := by
    have h := congrArg Subtype.val (C.originalPointDiffeomorph.apply_symm_apply (e x))
    exact h
  intro x
  have hd := mfderiv_comp (f := iP) (g := C.originalInclusion.map) x
    (C.originalInclusion.map.contMDiff.mdifferentiableAt (by simp))
    (hiP.mdifferentiableAt (by simp))
  rw [show C.originalInclusion.map ∘ iP = (fun y => (e y).val) from funext heP,
    mfderiv_originalInclusion] at hd
  change mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model d) (fun y => (e y).val) x =
    mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model d) iP x at hd
  change (C.localizedDomain.liouville.primitive (iP x)).compContinuousLinearMap
    (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model d) iP x) = lam x
  rw [C.original_primitive, ← hd]
  change (D.liouville.primitive (C.originalInclusion.map (iP x))).compContinuousLinearMap
    (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model d) (fun y => (e y).val) x) = _
  rw [heP]
  exact hpull x

end LocalizedPrimitive

end FsFltz.Geometry.IntrinsicLiouville
