import FsFltz.Geometry.IntrinsicMapPresentation
import FsFltz.Geometry.IntrinsicLiouvilleDomainExtension

/-!
# Native Liouville presentations retaining manifold-valued map extensions

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and
`sec:lean`, lines 783–814. The source-derived map extension presentation
is restricted to its actual open symplectic locus. Native carrier,
primitive, exterior derivative, Liouville field and scalar extensions are
preserved on that same presentation. Each manifold-valued map's open
neighborhood is pulled back to the restricted extension, retaining every
original carrier point and its prescribed map value.

This positive-dimensional foundation producer supplies no completion,
compact bundle family, full-fiber marking or geometric comparison chain.
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

/-- The source-derived primitive and universal map presentation carries its
actual symplectic derivative on the same compact carrier. No second domain
or stronger source premise is selected to obtain scalar or map extensions. -/
theorem exists_compactDomain_with_native_symplectic_and_map_extensions
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
      (∀ f : M → ℝ, IsLocallyExtendibleScalar (k := k) f →
        ∃ g : D.extension.Point → ℝ,
          ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ g ∧ ∀ x, g (i x) = f x) ∧
      ∀ (d : ℕ) (N : SmoothManifold d) (f : M → N.Point),
        IsLocallyExtendibleMap (k := k) (F := Model d) f →
        ∃ (W : TopologicalSpace.Opens D.extension.Point) (hW : range i ⊆ W)
          (g : W → N.Point),
          ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) ∞ g ∧
          ∀ x, g ⟨i x, hW ⟨x, rfl⟩⟩ = f x := by
  obtain ⟨D, i, lam, e, he, hi, hemb, hbij, hrange, hfrontier, hlam, hpull, hscalar, hmap⟩ :=
    exists_compactDomain_with_native_primitive_and_map_extensions α hα hnd hout
  have hd := exteriorDerivative_pullback_from_boundaryless D.extension i hi lam hlam
  rw [hpull] at hd
  refine ⟨D, i, lam, e, he, hi, hemb, hbij, hrange, hfrontier,
    hlam, hpull, hd.symm, ?_, hscalar, hmap⟩
  apply (D.extension.isSymplecticOn_exteriorDerivative_iff lam hlam D.carrier).mpr
  intro z hz
  rw [← hrange] at hz
  obtain ⟨x, rfl⟩ := hz
  exact nondegenerate_exteriorDerivative_of_native_pullback D.extension i hi lam hlam α
    hpull x (hbij x) (hnd x)

/-- One source-derived native Liouville presentation simultaneously
preserves the primitive, full exterior derivative, field and native carrier
diffeomorphism, and extends every source-smooth scalar or manifold-valued map.
Scalar extensions are global; each map extends on its own open neighborhood
of the entire compact carrier within this same symplectic extension. -/
theorem exists_liouvilleDomain_with_native_presentation_and_map_extensions
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
    ∃ (L : LiouvilleDomain (k + 1)) (i : M → L.domain.extension.Point)
      (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M L.domain.Point ∞),
      (∀ x, (e x).val = i x) ∧
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i ∧
      Topology.IsClosedEmbedding i ∧
      (∀ x, Function.Bijective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) ∧
      range i = L.domain.carrier ∧
      frontier L.domain.carrier = i '' (𝓡∂ (k + 1)).boundary M ∧
      (fun x => (L.liouville.primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α ∧
      (fun x => (L.domain.extension.exteriorDerivative L.liouville.primitive (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = exteriorDerivative α ∧
      (∀ x, L.liouville.field (i x) =
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x
          (liouvilleVector α (exteriorDerivative α) x)) ∧
      L.domain.extension.IsSymplecticOn
        (L.domain.extension.exteriorDerivative L.liouville.primitive) univ ∧
      (∀ f : M → ℝ, IsLocallyExtendibleScalar (k := k) f →
        ∃ g : L.domain.extension.Point → ℝ,
          ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ g ∧ ∀ x, g (i x) = f x) ∧
      (∀ f : M → ℝ, IsLocallyExtendibleScalar (k := k) f → (∀ x, 0 < f x) →
        ∃ g : L.domain.extension.Point → ℝ,
          ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ g ∧
            (∀ y, 0 < g y) ∧ ∀ x, g (i x) = f x) ∧
      ∀ (d : ℕ) (N : SmoothManifold d) (f : M → N.Point),
        IsLocallyExtendibleMap (k := k) (F := Model d) f →
        ∃ (W : TopologicalSpace.Opens L.domain.extension.Point) (hW : range i ⊆ W)
          (g : W → N.Point),
          ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) ∞ g ∧
          ∀ x, g ⟨i x, hW ⟨x, rfl⟩⟩ = f x := by
  obtain ⟨D, i, lam, e, he, hi, hemb, hbij, hrange, hfrontier, hlam, hpull, hderiv, hsymp, hscalar, hmap⟩ :=
    exists_compactDomain_with_native_symplectic_and_map_extensions α hα hnd hout
  let hDnd := hsymp.2.2
  let U := D.symplecticNeighborhood lam hlam
  let D' := D.symplecticRestriction lam hlam hDnd
  let := D'.halfSpaceChartedSpace
  let e' : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M D'.Point ∞ :=
    e.trans (D.restrictPointDiffeomorph U
      (D.carrier_subset_symplecticNeighborhood lam hlam hDnd)).symm
  let j : M → D'.extension.Point := fun x => (e' x).val
  have hjval (x : M) : (j x).val = i x := by
    change (e x).val = i x
    exact he x
  have hval : (Subtype.val : D'.extension.Point → D.extension.Point) ∘ j = i :=
    funext hjval
  have hj : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ j :=
    D'.contMDiff_subtype_val.comp e'.contMDiff
  have hjemb : Topology.IsClosedEmbedding j :=
    Topology.IsClosedEmbedding.of_comp Topology.IsEmbedding.subtypeVal (hval ▸ hemb)
  have hdj (x : M) : mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j x =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x := by
    have hd := mfderiv_comp (f := j)
      (g := (Subtype.val : D'.extension.Point → D.extension.Point)) x
      ((D.extension.restrictInclusion U).map.contMDiff.mdifferentiableAt (by simp))
      (hj.mdifferentiableAt (by simp))
    rw [hval] at hd
    erw [D.extension.mfderiv_restrict_val U (j x)] at hd
    exact hd.symm
  have hjbij (x : M) : Function.Bijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j x) := by
    rw [hdj]
    exact hbij x
  have hjrange : range j = D'.carrier := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      change (j x).val ∈ D.carrier
      rw [hjval, ← hrange]
      exact mem_range_self x
    · intro hy
      change y.val ∈ D.carrier at hy
      rw [← hrange] at hy
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext ((hjval x).trans hx)⟩
  have hjfrontier : frontier D'.carrier = j '' (𝓡∂ (k + 1)).boundary M := by
    rw [D.frontier_restrict_carrier U, hfrontier]
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, Subtype.ext ((hjval x).trans hxy)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hjval x).symm⟩
  let lam' := D.symplecticRestrictionPrimitive lam hlam hDnd
  let F := D.symplecticRestrictionField lam hlam hDnd
  have hpull' : (fun x => (lam' (j x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j x)) = α := by
    funext x
    dsimp only [lam']
    rw [D.symplecticRestrictionPrimitive_val lam hlam hDnd (j x), hjval, hdj]
    exact congrFun hpull x
  have hderiv' : (fun x => (D'.extension.exteriorDerivative lam' (j x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j x)) = exteriorDerivative α := by
    funext x
    rw [D.exteriorDerivative_symplecticRestrictionPrimitive lam hlam hDnd (j x), hjval, hdj]
    exact congrFun hderiv x
  have hfield' (x : M) : F (j x) =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) j x
        (liouvilleVector α (exteriorDerivative α) x) := by
    apply liouvilleVector_extension_eq D'.extension j α lam' hnd
      (congrFun hpull') (congrFun hderiv') x (hjbij x).2
    exact D.nondegenerate_symplecticRestrictionPrimitive lam hlam hDnd (j x)
  have hnegative (b : IntrinsicBoundary.Point k M) :
      (show Model (k + 1) from chartTangentMap (IntrinsicBoundary.chartAt b).ambient
        b.val (liouvilleVector α (exteriorDerivative α) b.val)) 0 < 0 := by
    obtain ⟨rho, beta, hz, hs, hr, hb, hag, hpos⟩ := hout b
    have hesource : b.val ∈ (IntrinsicBoundary.chartAt b).ambient.source := by
      have h := IntrinsicBoundary.mem_chartAt_source b
      rwa [(IntrinsicBoundary.chartAt b).source_eq] at h
    exact (outward_iff_negative_normal_of_localDefiningFunction
      (IntrinsicBoundary.chartAt b).mem_atlas hesource b.property rho hz hs hr hb hag
      (liouvilleVector α (exteriorDerivative α) b.val)).mp hpos
  have hout' : ∀ (y : D'.extension.Point) (hy : y ∈ frontier D'.carrier),
      0 < D'.extension.scalarDerivative (D'.defining y hy).rho y (F y) :=
    outward_compactDomain_extension D' j hj (fun x => (hjbij x).2) hjrange hjfrontier
      (liouvilleVector α (exteriorDerivative α)) F hfield' hnegative
  have hglobal := D.isSymplecticOn_symplecticRestrictionPrimitive lam hlam hDnd
  let L : LiouvilleDomain (k + 1) :=
    { domain := D'
      liouville :=
        { primitive := lam'
          smooth_primitive := D.isSmoothForm_symplecticRestrictionPrimitive lam hlam hDnd
          symplectic := ⟨hglobal.1, fun x _ => hglobal.2.1 x (mem_univ x),
            fun x _ => hglobal.2.2 x (mem_univ x)⟩
          field := F
          smooth_field := D.isSmoothVectorField_symplecticRestrictionField lam hlam hDnd
          contraction := fun x _ v => D.symplecticRestrictionField_contraction lam hlam hDnd x v
          outward := hout' } }
  have hscalar' : ∀ f : M → ℝ, IsLocallyExtendibleScalar (k := k) f →
      ∃ g : L.domain.extension.Point → ℝ,
        ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ g ∧ ∀ x, g (j x) = f x := by
    intro f hf
    obtain ⟨g, hg, heq⟩ := hscalar f hf
    refine ⟨g ∘ Subtype.val,
      hg.comp (D.extension.restrictInclusion U).map.contMDiff, ?_⟩
    intro x
    change g (j x).val = f x
    rw [hjval]
    exact heq x
  refine ⟨L, j, e', fun _ => rfl, hj, hjemb, hjbij, hjrange, hjfrontier,
    hpull', hderiv', hfield', hglobal, hscalar', ?_, ?_⟩
  · intro f hf hpos
    exact exists_positive_scalarExtension L.domain.extension j hscalar' hf hpos
  · intro d N f hf
    obtain ⟨W, hW, g, hg, heq⟩ := hmap d N f hf
    let W' : TopologicalSpace.Opens L.domain.extension.Point :=
      ⟨Subtype.val ⁻¹' W, W.isOpen.preimage continuous_subtype_val⟩
    have hW' : range j ⊆ W' := by
      rintro y ⟨x, rfl⟩
      change (j x).val ∈ W
      rw [hjval]
      exact hW ⟨x, rfl⟩
    let a : W' → W := fun y => ⟨y.val.val, y.property⟩
    have ha : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ a :=
      (ContMDiff.subtypeVal_comp_iff W a).mp
        ((D.extension.restrictInclusion U).map.contMDiff.comp contMDiff_subtype_val)
    refine ⟨W', hW', g ∘ a, hg.comp ha, ?_⟩
    intro x
    change g ⟨(j x).val, _⟩ = f x
    simpa only [hjval] using heq x


end FsFltz.Geometry.IntrinsicLiouville
