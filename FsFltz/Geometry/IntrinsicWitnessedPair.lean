import FsFltz.Geometry.IntrinsicLiouvilleBoundaryPresentation
import FsFltz.Geometry.IntrinsicMapComposition

/-!
# Witnessed pairs from native ambient and ribbon data

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The ambient and ribbon primitives are native tangent forms.
The ambient Liouville presentation first constructs its actual boundary
diffeomorphism from the same inclusion. Transport of the prescribed ribbon
map and positive witness through that diffeomorphism retains their full
primitive identity. The native ribbon producer then constructs the extended
embedding, both collars, and both completions.

This foundational correspondence does not construct the far-fiber ribbon,
its marking onto a specified full fiber, or the geometric comparison chain.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

section PositiveRibbon

variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {A M : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A]
  [IsManifold (𝓡∂ (a + 1)) ∞ A]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Native ambient and positive-dimensional ribbon data construct an actual
witnessed pair. The native compact diffeomorphisms, boundary inclusion square,
both original primitives, prescribed witness and full ribbon map are retained
on the same localized pair and its constructed completions. -/
theorem exists_intrinsic_witnessedPair
    (hdimA : a + 1 = 2 * n) (hdimM : k + 1 = 2 * n - 2)
    (lam : Form a A 1) (hlam : IsLocallyExtendibleForm lam)
    (hAnd : ∀ x, Nondegenerate (exteriorDerivative lam) x)
    (hAout : ∀ x : IntrinsicBoundary.Point a A,
      ∃ (rho : A → ℝ) (beta : Model (a + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (a + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector lam (exteriorDerivative lam) x.val)))
    (μ : Form k M 1) (hμ : IsLocallyExtendibleForm μ)
    (hMnd : ∀ x, Nondegenerate (exteriorDerivative μ) x)
    (hMout : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector μ (exteriorDerivative μ) x.val)))
    (j : M → IntrinsicBoundary.Point a A)
    (hjs : IsLocallyExtendibleMap (k := k) (F := Model a) j)
    (hjinj : Function.Injective j)
    (hjimm : ∀ x, Function.Injective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) j x))
    (b : IntrinsicBoundary.Point a A → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model a) 𝓘(ℝ, ℝ) ∞ b)
    (hpositive : ∀ x, 0 < b x)
    (hribbon : ∀ x,
      ((b (j x) • IntrinsicBoundary.restrictForm lam (j x))).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) j x) = μ x) :
    ∃ (P : WitnessedPair n)
      (eA : Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (2 * n)) A P.ambientDomain.domain.Point ∞)
      (eM : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M P.ribbonDomain.domain.Point ∞)
      (eB : (IntrinsicBoundary.smoothManifold a A).SmoothEquiv P.ambientDomain.domain.boundary),
      (∀ x, P.ambientDomain.domain.boundaryInclusion.map (eB x) = (eA x.val).val) ∧
      (∀ x, (P.ambientDomain.liouville.primitive (eA x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eA y).val) x) = lam x) ∧
      (IntrinsicBoundary.smoothManifold a A).pullback P.ambientDomain.domain.boundary eB
        (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
          IntrinsicBoundary.restrictForm lam ∧
      (∀ x, P.ribbonEmbedding.map (eM x).val = eB (j x)) ∧
      (∀ x, P.witness (eB x) = b x) ∧
      (∀ x, (P.ribbonDomain.liouville.primitive (eM x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eM y).val) x) = μ x) ∧
      P.ribbonEmbedding.map '' P.ribbonDomain.domain.carrier = eB '' range j ∧
      P.embeddedCore = (fun x => eB (j x)) '' {x | ∀ t : ℝ, 0 ≤ t →
        P.ribbonCompletion.ambient.completeFlow.flow t
          (P.ribbonCompletion.inclusion.map (eM x).val) ∈
            range (fun y => P.ribbonCompletion.inclusion.map (eM y).val)} := by
  obtain ⟨D, iA, eA, eB, heA, hiA, hdiA, hrangeA, hpullA, hBinclusion, hpullB⟩ :=
    native_boundary_presentation_dimension_eq hdimA lam
      (exists_liouvilleDomain_with_native_boundary_presentation lam hlam hAnd hAout)
  let j' : M → D.domain.boundary.Point := eB ∘ j
  let b' : D.domain.boundary.Point → ℝ := b ∘ eB.symm
  have hjs' : IsLocallyExtendibleMap (k := k) (F := Model (2 * n - 1)) j' :=
    hjs.comp_contMDiff (IntrinsicBoundary.smoothManifold a A) D.domain.boundary eB eB.contMDiff
  have hjinj' : Function.Injective j' := eB.injective.comp hjinj
  have hjimm' (x : M) : Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) j' x) := by
    rw [mfderiv_comp x (eB.contMDiff.mdifferentiableAt (by simp))
      ((contMDiff_of_isLocallyExtendibleMap hjs).mdifferentiableAt (by simp))]
    exact (eB.mfderivToContinuousLinearEquiv (by simp) (j x)).injective.comp (hjimm x)
  have hb' : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ b' := hb.comp eB.symm.contMDiff
  have hpositive' (x : D.domain.boundary.Point) : 0 < b' x := hpositive (eB.symm x)
  have hribbon' (x : M) :
      ((b' (j' x) • D.domain.boundaryForm D.liouville.primitive (j' x))).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) j' x) = μ x := by
    have hd := mfderiv_comp (f := j) (g := eB) x
      (eB.contMDiff.mdifferentiableAt (by simp))
      ((contMDiff_of_isLocallyExtendibleMap hjs).mdifferentiableAt (by simp))
    have hform := congrFun hpullB (j x)
    rw [← hribbon x]
    ext vs
    change b (eB.symm (eB (j x))) *
        D.domain.boundaryForm D.liouville.primitive (eB (j x))
          (fun u => mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (eB ∘ j) x (vs u)) =
      b (j x) * IntrinsicBoundary.restrictForm lam (j x)
        (fun u => mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model a) j x (vs u))
    rw [eB.symm_apply_apply, hd, ← hform]
    rfl
  obtain ⟨F, iM, eM, q, heM, hiM, hdiM, hrangeM, hqj, hpullM, hprimitive,
    CA, CM, eMP, heMP, hjMP, himage, hwitness, hprimitiveMP, hcore⟩ :=
    exists_native_witnessedPair hdimM μ hμ hMnd hMout D j' hjs' hjinj' hjimm'
      b' hb' hpositive' hribbon'
  let P := localizedWitnessedPair D F CA CM q b' hb' hpositive' hprimitive
  let eAP := eA.trans CA.originalPointDiffeomorph.symm
  have heAP (x : A) : (eAP x).val.val.val = iA x := by
    have h := congrArg Subtype.val (CA.originalPointDiffeomorph.apply_symm_apply (eA x))
    exact h.trans (heA x)
  have hprimitiveAP : ∀ x,
      (P.ambientDomain.liouville.primitive (eAP x).val).compContinuousLinearMap
        (mfderiv (𝓡∂ (a + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAP y).val) x) = lam x := by
    apply native_primitive_localizedDomain D CA eA lam
    intro x
    rw [heA x, show (fun y => (eA y).val) = iA from funext heA]
    exact congrFun hpullA x
  refine ⟨P, eAP, eMP, eB, ?_, hprimitiveAP, ?_, hjMP, ?_, hprimitiveMP, ?_, hcore⟩
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    exact (hBinclusion x).trans (heAP x.val).symm
  · change (IntrinsicBoundary.smoothManifold a A).pullback D.domain.boundary eB
      (CA.localizedDomain.domain.boundaryForm CA.localizedDomain.liouville.primitive) = _
    rw [CA.localized_boundaryForm]
    exact hpullB
  · intro x
    change b (eB.symm (eB x)) = b x
    rw [eB.symm_apply_apply]
  · rw [himage]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨j x, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩

end PositiveRibbon

end FsFltz.Geometry.IntrinsicLiouville
