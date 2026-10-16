import FsFltz.Geometry.IntrinsicZeroRibbonPair
import FsFltz.Geometry.IntrinsicLiouvilleBoundaryPresentation

/-!
# Rank-one witnessed pairs from fully native data

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, especially the
zero-dimensional ribbon and its entire core at lines 159–160; `sec:lean`,
lines 783–814 and 825–830. A native Liouville surface constructs its compact
and boundary presentations through the same inclusion. A compact native
zero-dimensional ribbon and its prescribed injective boundary map then
construct an actual witnessed pair with both completions. The arbitrary
native ribbon primitive vanishes algebraically.

The native ambient and ribbon maps, boundary primitive, positive witness,
entire ribbon image and full core are preserved. No full-fiber marking or
geometric comparison chain is asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicZeroLiouville

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]

/-- The rank-one pair's actual compact ribbon retains the original native
zero-dimensional atlas through its two compact carrier diffeomorphisms. -/
def witnessedPairCarrierDiffeomorph
    (D : LiouvilleDomain 2) (j : M → D.domain.boundary.Point)
    (hj : Function.Injective j) (b : D.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model 1) 𝓘(ℝ, ℝ) ∞ b)
    (hpositive : ∀ x, 0 < b x) :
    letI := (witnessedPair D j hj b hb hpositive).ribbonDomain.domain.zeroChartedSpace
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M
      (witnessedPair D j hj b hb hpositive).ribbonDomain.domain.Point ∞ := by
  let := (witnessedPair D j hj b hb hpositive).ribbonDomain.domain.zeroChartedSpace
  let := (liouvilleDomain M 0).domain.zeroChartedSpace
  let := (liouvilleDomain M 0).carrierRestriction_of_dimension_zero.domain.zeroChartedSpace
  exact (carrierDiffeomorph (M := M) 0).trans
    (liouvilleDomain M 0).carrierRestrictionDiffeomorph_of_dimension_zero.symm

/-- The compact ribbon diffeomorphism retains every original native point. -/
@[simp] theorem witnessedPairCarrierDiffeomorph_val
    (D : LiouvilleDomain 2) (j : M → D.domain.boundary.Point)
    (hj : Function.Injective j) (b : D.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model 1) 𝓘(ℝ, ℝ) ∞ b)
    (hpositive : ∀ x, 0 < b x) (x : M) :
    (witnessedPairCarrierDiffeomorph D j hj b hb hpositive x).val.val = x := rfl

/-- The arbitrary native zero-dimensional one-form is preserved by the
actual rank-one pair's compact ribbon equivalence. -/
theorem witnessedPairCarrierDiffeomorph_primitive
    (D : LiouvilleDomain 2) (j : M → D.domain.boundary.Point)
    (hj : Function.Injective j) (b : D.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model 1) 𝓘(ℝ, ℝ) ∞ b)
    (hpositive : ∀ x, 0 < b x) (μ : (sourceManifold M).Form 1) :
    (sourceManifold M).pullback (witnessedPair D j hj b hb hpositive).ribbonDomain.domain.extension
      (fun y => (witnessedPairCarrierDiffeomorph D j hj b hb hpositive y).val)
      (witnessedPair D j hj b hb hpositive).ribbonDomain.liouville.primitive = μ := by
  rw [positiveForm_eq_zero M 0 ((sourceManifold M).pullback _ _ _), positiveForm_eq_zero M 0 μ]

variable {A : Type} [TopologicalSpace A] [T2Space A]
  [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace 2) A] [IsManifold (𝓡∂ 2) ∞ A]

/-- Fully native surface and zero-dimensional ribbon data construct an
actual rank-one pair. Both compact carrier diffeomorphisms and the ambient
boundary diffeomorphism retain the prescribed map, witness and primitives.
The full embedded core is the entire original ribbon image. -/
theorem exists_native_zero_witnessedPair
    (lam : IntrinsicLiouville.Form 1 A 1)
    (hlam : IntrinsicLiouville.IsLocallyExtendibleForm lam)
    (hnd : ∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative lam) x)
    (hout : ∀ x : IntrinsicBoundary.Point 1 A,
      ∃ (rho : A → ℝ) (beta : Model 2 → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2)).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ 2)).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) rho x.val
          (IntrinsicLiouville.liouvilleVector lam (IntrinsicLiouville.exteriorDerivative lam) x.val)))
    (μ : (sourceManifold M).Form 1) (j : M → IntrinsicBoundary.Point 1 A)
    (hj : Function.Injective j)
    (b : IntrinsicBoundary.Point 1 A → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model 1) 𝓘(ℝ, ℝ) ∞ b) (hpositive : ∀ x, 0 < b x) :
    ∃ (D : LiouvilleDomain 2) (i : A → D.domain.extension.Point)
      (e : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A D.domain.Point ∞)
      (eB : (IntrinsicBoundary.smoothManifold 1 A).SmoothEquiv D.domain.boundary),
      (∀ x, (e x).val = i x) ∧
      ContMDiff (𝓡∂ 2) 𝓘(ℝ, Model 2) ∞ i ∧
      (∀ x, Function.Bijective (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) i x)) ∧
      range i = D.domain.carrier ∧
      (fun x => (D.liouville.primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) i x)) = lam ∧
      (∀ x, D.domain.boundaryInclusion.map (eB x) = i x.val) ∧
      (IntrinsicBoundary.smoothManifold 1 A).pullback D.domain.boundary eB
        (D.domain.boundaryForm D.liouville.primitive) = IntrinsicBoundary.restrictForm lam ∧
      ∃ (hj' : Function.Injective (eB ∘ j))
        (hb' : ContMDiff 𝓘(ℝ, Model 1) 𝓘(ℝ, ℝ) ∞ (b ∘ eB.symm))
        (hpositive' : ∀ x, 0 < (b ∘ eB.symm) x),
      let P := witnessedPair D (eB ∘ j) hj' (b ∘ eB.symm) hb' hpositive'
      letI := P.ribbonDomain.domain.zeroChartedSpace
      ∃ (eA : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A P.ambientDomain.domain.Point ∞)
        (eF : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M P.ribbonDomain.domain.Point ∞),
        (∀ x, (eA x).val.val.val = i x) ∧ (∀ x, (eF x).val.val = x) ∧
        (∀ x, P.ambientDomain.domain.boundaryInclusion.map (eB x) = (eA x.val).val) ∧
        (∀ x, P.ribbonEmbedding.map (eF x).val = eB (j x)) ∧
        (∀ x, P.ambientDomain.domain.boundaryInclusion.map (P.ribbonEmbedding.map (eF x).val) =
          (eA (j x).val).val) ∧
        (∀ x, P.witness (eB x) = b x) ∧
        P.ribbonEmbedding.map '' P.ribbonDomain.domain.carrier = eB '' range j ∧
        P.embeddedCore = eB '' range j ∧
        (∀ x, (P.ambientDomain.liouville.primitive (eA x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ 2) 𝓘(ℝ, Model 2) (fun y => (eA y).val) x) = lam x) ∧
        (sourceManifold M).pullback P.ribbonDomain.domain.extension (fun y => (eF y).val)
          P.ribbonDomain.liouville.primitive = μ ∧
        (IntrinsicBoundary.smoothManifold 1 A).pullback P.ambientDomain.domain.boundary eB
          (P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive) =
          IntrinsicBoundary.restrictForm lam := by
  obtain ⟨D, i, e, eB, he, hi, hdi, hrange, hpull, hBinclusion, hpullB⟩ :=
    IntrinsicLiouville.exists_liouvilleDomain_with_native_boundary_presentation lam hlam hnd hout
  have hj' : Function.Injective (eB ∘ j) := eB.injective.comp hj
  have hb' : ContMDiff 𝓘(ℝ, Model 1) 𝓘(ℝ, ℝ) ∞ (b ∘ eB.symm) := hb.comp eB.symm.contMDiff
  have hpositive' : ∀ x, 0 < (b ∘ eB.symm) x := fun x => hpositive (eB.symm x)
  let P := witnessedPair D (eB ∘ j) hj' (b ∘ eB.symm) hb' hpositive'
  let C := D.flowCollar
  let eA : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) A P.ambientDomain.domain.Point ∞ :=
    e.trans C.originalPointDiffeomorph.symm
  let := P.ribbonDomain.domain.zeroChartedSpace
  let eF : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M P.ribbonDomain.domain.Point ∞ :=
    witnessedPairCarrierDiffeomorph D (eB ∘ j) hj' (b ∘ eB.symm) hb' hpositive'
  have heA (x : A) : (eA x).val.val.val = i x := he x
  have hboundary (x : IntrinsicBoundary.Point 1 A) :
      P.ambientDomain.domain.boundaryInclusion.map (eB x) = (eA x.val).val := by
    apply C.originalInclusion.embedding.injective
    change D.domain.boundaryInclusion.map (eB x) = (eA x.val).val.val.val
    rw [heA]
    exact hBinclusion x
  have hjF (x : M) : P.ribbonEmbedding.map (eF x).val = eB (j x) := rfl
  have hcompRange : range (eB ∘ j) = eB '' range j := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨j x, mem_range_self x, rfl⟩
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
  refine ⟨D, i, e, eB, he, hi, hdi, hrange, hpull, hBinclusion, hpullB,
    hj', hb', hpositive', eA, eF, heA, fun _ => rfl, hboundary, hjF, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hjF]
    exact hboundary (j x)
  · intro x
    change b (eB.symm (eB x)) = b x
    rw [eB.symm_apply_apply]
  · rw [← hcompRange]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, hx⟩ := eF.surjective ⟨z, hz⟩
      exact ⟨x, (hjF x).symm.trans (congrArg (fun w => P.ribbonEmbedding.map w.val) hx)⟩
    · rintro ⟨x, rfl⟩
      exact ⟨(eF x).val, (eF x).property, hjF x⟩
  · exact (witnessedPair_embeddedCore D (eB ∘ j) hj' (b ∘ eB.symm) hb' hpositive').trans hcompRange
  · apply IntrinsicLiouville.native_primitive_localizedDomain D C e lam
    intro x
    rw [show (fun y => (e y).val) = i from funext he, he]
    exact congrFun hpull x
  · exact witnessedPairCarrierDiffeomorph_primitive D (eB ∘ j) hj' (b ∘ eB.symm) hb' hpositive' μ
  · change (IntrinsicBoundary.smoothManifold 1 A).pullback D.domain.boundary eB
      (C.localizedDomain.domain.boundaryForm C.localizedDomain.liouville.primitive) = _
    rw [C.localized_boundaryForm]
    exact hpullB

end FsFltz.Geometry.IntrinsicZeroLiouville
