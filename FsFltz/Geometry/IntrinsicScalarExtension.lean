import FsFltz.Geometry.IntrinsicCollarDefining
import FsFltz.Geometry.SmoothScalarExtension
import FsFltz.Geometry.IntrinsicLiouvilleSeam
import FsFltz.Geometry.IntrinsicLiouvilleGluing
import FsFltz.Geometry.IntrinsicCollarDomain
import FsFltz.Geometry.IntrinsicGluedFormRestriction
import FsFltz.Geometry.IntrinsicCollarPresentation

/-!
# Scalar extension on the native collar quotient

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and
`sec:lean`, lines 783–814. Local scalar extensions on the two-sided collar
are transported through the actual smooth cylinder inverse. The global
partition-of-unity extension preserves all original carrier values.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Source scalar smoothness across a native boundary: in every native
chart its coefficient has an actual smooth extension on an open model
neighborhood. No global ambient scalar or presentation is assumed. -/
def IsLocallyExtendibleScalar (f : M → ℝ) : Prop :=
  ∀ e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)),
    e ∈ atlas (EuclideanHalfSpace (k + 1)) M → ∀ x ∈ e.source,
      ∃ (β : Model (k + 1) → ℝ) (U : Set (Model (k + 1))),
        IsOpen U ∧ e.extend (𝓡∂ (k + 1)) x ∈ U ∧ ContDiffOn ℝ ∞ β U ∧
        β =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target]
          (e.extend (𝓡∂ (k + 1)) x)] (f ∘ (e.extend (𝓡∂ (k + 1))).symm)

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- A positive source scalar has a locally extendible logarithm. Each actual
chart extension is restricted to its open positive locus. -/
theorem IsLocallyExtendibleScalar.log {f : M → ℝ}
    (hf : IsLocallyExtendibleScalar (k := k) f) (hpos : ∀ x, 0 < f x) :
    IsLocallyExtendibleScalar (k := k) (Real.log ∘ f) := by
  intro e he x hx
  obtain ⟨β, U, hU, hxU, hβ, heq⟩ := hf e he x hx
  have ht : e.extend (𝓡∂ (k + 1)) x ∈ (e.extend (𝓡∂ (k + 1))).target :=
    (e.extend (𝓡∂ (k + 1))).map_source (by simpa only [e.extend_source] using hx)
  have hval : β (e.extend (𝓡∂ (k + 1)) x) = f x := by
    have h := heq.eq_of_nhdsWithin ht
    simpa only [Function.comp_apply, e.extend_left_inv hx] using h
  let V := U ∩ β ⁻¹' Ioi 0
  have hVo : IsOpen V := hβ.continuousOn.isOpen_inter_preimage hU isOpen_Ioi
  have hxV : e.extend (𝓡∂ (k + 1)) x ∈ V := ⟨hxU, by simpa only [mem_preimage, mem_Ioi, hval] using hpos x⟩
  refine ⟨Real.log ∘ β, V, hVo, hxV, ?_, ?_⟩
  · exact (hβ.mono inter_subset_left).log (fun y hy => ne_of_gt hy.2)
  · filter_upwards [heq] with y hy
    exact congrArg Real.log hy

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Universal scalar extension on one fixed presentation yields a globally
positive smooth extension of each positive source scalar, on that same
ambient manifold. Exponentiating the extended logarithm preserves every
source value and requires no new ambient restriction. -/
theorem exists_positive_scalarExtension {d : ℕ} (N : SmoothManifold d)
    (i : M → N.Point)
    (hscalar : ∀ f : M → ℝ, IsLocallyExtendibleScalar (k := k) f →
      ∃ g : N.Point → ℝ, ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ g ∧
        ∀ x, g (i x) = f x)
    {f : M → ℝ} (hf : IsLocallyExtendibleScalar (k := k) f) (hpos : ∀ x, 0 < f x) :
    ∃ g : N.Point → ℝ, ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ g ∧
      (∀ y, 0 < g y) ∧ ∀ x, g (i x) = f x := by
  obtain ⟨a, ha, heq⟩ := hscalar (Real.log ∘ f) (hf.log hpos)
  refine ⟨Real.exp ∘ a, Real.contDiff_exp.contMDiff.comp ha,
    fun y => Real.exp_pos (a y), ?_⟩
  intro x
  change Real.exp (a (i x)) = f x
  rw [heq x]
  exact Real.exp_log (hpos x)

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Actual chart extension germs imply native manifold smoothness. -/
theorem contMDiff_of_isLocallyExtendibleScalar {f : M → ℝ}
    (hf : IsLocallyExtendibleScalar (k := k) f) : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) ∞ f := by
  intro x
  let e := chartAt (EuclideanHalfSpace (k + 1)) x
  have hx : x ∈ e.source := mem_chart_source _ _
  obtain ⟨β, U, hU, hxU, hβ, heq⟩ := hf e (chart_mem_atlas _ x) x hx
  have ht : e.extend (𝓡∂ (k + 1)) x ∈ (e.extend (𝓡∂ (k + 1))).target :=
    (e.extend (𝓡∂ (k + 1))).map_source (by simpa only [e.extend_source] using hx)
  have heqpoint := heq.eq_of_nhdsWithin ht
  rw [e.nhdsWithin_extend_target_eq hx] at heq
  apply contMDiffAt_iff_source.mpr
  exact ((hβ.contDiffAt (hU.mem_nhds hxU)).contMDiffAt.contMDiffWithinAt).congr_of_eventuallyEq
    heq.symm heqpoint.symm

end FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicCollarGluing

private theorem exists_scalar_on_open_patch
    {E U X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace U] [TopologicalSpace X] [ChartedSpace E U] [ChartedSpace E X]
    [IsManifold 𝓘(ℝ, E) ∞ U] [IsManifold 𝓘(ℝ, E) ∞ X]
    {i : U → X} (hi : IsOpenEmbedding i) (u : U)
    (hatlas : ∀ q : U, (chartAt E q).lift_openEmbedding hi ∈
      IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ X)
    {f : U → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    ∃ g : X → ℝ, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g (range i) ∧
      ∀ q, g (i q) = f q := by
  let : Nonempty U := ⟨u⟩
  let inv : X → U := (hi.toOpenPartialHomeomorph i).symm
  have hinv : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ inv (range i) := by
    rintro z ⟨q, rfl⟩
    obtain ⟨g, hg, _, heq⟩ := smooth_inverse_germ_of_lifted_chart hi q (hatlas q)
    apply (hg.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [heq] with z hz
    exact (congrArg inv hz).symm.trans
      (hi.toOpenPartialHomeomorph_left_inv i)
  refine ⟨f ∘ inv, hf.comp_contMDiffOn hinv, ?_⟩
  intro q
  change f (inv (i q)) = f q
  exact congrArg f (hi.toOpenPartialHomeomorph_left_inv i)

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val))
  (hC : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
    (Half δ (IntrinsicBoundary.Point k M)))
  (hboundary : ∀ p : Half δ (IntrinsicBoundary.Point k M),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C p.val) ↔ p.val.1 = 0)
  (hinv : ∀ p ∈ Half δ (IntrinsicBoundary.Point k M),
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C q) = q)
  (hzero : ∀ b : IntrinsicBoundary.Point k M, C (0, b) = b.val)

local instance : ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ

local instance : IsManifold 𝓘(ℝ, Model (k + 1)) ∞ (Band δ (IntrinsicBoundary.Point k M)) :=
  band_isManifold δ

/-- Scalar germs on genuine open two-sided collar neighborhoods, together
with native smoothness, produce one global smooth function on the actual
collar quotient. Every value on the original carrier is preserved exactly.
The collar germs may disagree off the nonnegative half. -/
theorem exists_scalarExtension_of_collar_germs
    {f : M → ℝ} (hf : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hseam : ∀ b : IntrinsicBoundary.Point k M,
      ∃ a : ℝ × IntrinsicBoundary.Point k M → ℝ,
      ∃ W : Set (ℝ × IntrinsicBoundary.Point k M),
        IsOpen W ∧ (0, b) ∈ W ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) 𝓘(ℝ, ℝ) ∞ a W ∧
        EqOn a (fun p => f (C p)) (W ∩ Half δ (IntrinsicBoundary.Point k M))) :
    ∃ g : (extensionManifold hδ C hemb hC hboundary hinv hzero).Point → ℝ,
      ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ g ∧
      ∀ x, g (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x) = f x := by
  classical
  let X := extensionManifold hδ C hemb hC hboundary hinv hzero
  let C₀ := fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val
  let i := original C₀
  let := extensionChartedSpace hδ C hemb hboundary hzero
  let := extension_isManifold hδ C hemb hC hboundary hinv hzero
  let : T2Space (Extension C₀) := t2Space_extension hδ C₀ hemb
  let : SecondCountableTopology (Extension C₀) :=
    secondCountableTopology_extension hδ C₀ hemb hboundary hzero
  let F : Extension C₀ → ℝ := fun z => if hz : ∃ x, i x = z then f hz.choose else 0
  have hFi (x : M) : F (i x) = f x := by
    have hx : ∃ y, i y = i x := ⟨x, rfl⟩
    have he := (isClosedEmbedding_original hδ C₀ hemb).injective hx.choose_spec
    simp only [F, dite_eq_left hx, he]
  have hlocal : ∀ z ∈ range i, ∃ U ∈ 𝓝 z, ∃ g : Extension C₀ → ℝ,
      ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ g U ∧ EqOn g F (U ∩ range i) := by
    rintro z ⟨x, rfl⟩
    rcases (𝓡∂ (k + 1)).isInteriorPoint_or_isBoundaryPoint x with hx | hx
    · let u : IntrinsicInterior.Point k M := ⟨x, hx⟩
      let j := interiorIn C₀
      have hj := isOpenEmbedding_interiorIn hδ C₀ hemb hboundary
      have ha (q : IntrinsicInterior.Point k M) :
          (chartAt (Model (k + 1)) q).lift_openEmbedding hj ∈
            IsManifold.maximalAtlas 𝓘(ℝ, Model (k + 1)) ∞ (Extension C₀) := by
        apply IsManifold.subset_maximalAtlas
        exact Or.inl ⟨chartAt (Model (k + 1)) q, chart_mem_atlas _ q, rfl⟩
      obtain ⟨g, hg, heq⟩ := exists_scalar_on_open_patch hj u ha
        (hf.comp IntrinsicInterior.contMDiff_val)
      refine ⟨range j, hj.isOpen_range.mem_nhds (mem_range_self u), g, hg, ?_⟩
      rintro z ⟨⟨q, rfl⟩, _⟩
      exact (heq q).trans (hFi q.val).symm
    · let b : IntrinsicBoundary.Point k M := ⟨x, hx⟩
      let p : Band δ (IntrinsicBoundary.Point k M) :=
        ⟨(0, b), ⟨by linarith, hδ⟩, mem_univ _⟩
      let j := cylinder C₀
      let v := cylinderInverse hδ C₀ hemb p
      have hp : j p = i x := by
        symm
        apply (original_eq_cylinder_iff C₀ x p).mpr
        exact ⟨le_rfl, hzero b⟩
      obtain ⟨a, W, hWo, hpW, ha, heq⟩ := hseam b
      let U := range j ∩ (Subtype.val ∘ v) ⁻¹' W
      have hv := contMDiffOn_cylinderInverse hδ C hemb hC hboundary hinv hzero p
      have hvp := hv.contMDiffAt
        ((isOpenEmbedding_cylinder hδ C₀ hemb).isOpen_range.mem_nhds (mem_range_self p))
      have hnv : U ∈ 𝓝 (i x) := by
        rw [← hp]
        apply inter_mem ((isOpenEmbedding_cylinder hδ C₀ hemb).isOpen_range.mem_nhds
          (mem_range_self p))
        apply (continuous_subtype_val.continuousAt.comp hvp.continuousAt).preimage_mem_nhds
        change W ∈ 𝓝 (cylinderInverse hδ C₀ hemb p (cylinder C₀ p)).val
        rw [cylinderInverse_cylinder]
        exact hWo.mem_nhds hpW
      refine ⟨U, hnv, a ∘ Subtype.val ∘ v, ?_, ?_⟩
      · exact ha.comp ((contMDiff_band_val δ).comp_contMDiffOn
          (hv.mono inter_subset_left)) (fun _ hy => hy.2)
      · rintro z ⟨hz, y, rfl⟩
        have hyj : i y = j (v (i y)) :=
          (cylinder_cylinderInverse hδ C₀ hemb p hz.1).symm
        obtain ⟨ht, hCy⟩ := (original_eq_cylinder_iff C₀ y (v (i y))).mp hyj
        have hhalf : (v (i y)).val ∈ Half δ (IntrinsicBoundary.Point k M) :=
          ⟨⟨ht, (v (i y)).property.1.2⟩, mem_univ _⟩
        exact (heq ⟨hz.2, hhalf⟩).trans
          ((congrArg f hCy).trans (hFi y).symm)
  obtain ⟨g, hg, heq⟩ := exists_contMDiff_scalarExtension_of_closed
    (isClosed_range_original hδ C₀ hemb) hlocal
  exact ⟨g, hg, fun x => (heq (mem_range_self x)).trans (hFi x)⟩

/-- On a fixed actual Liouville collar, source primitive smoothness and
source scalar extension germs suffice to construct the global scalar
extension. The needed two-sided collar scalar germs are produced here. -/
theorem exists_scalarExtension_of_primitive_collar
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (hnd : ∀ x, IntrinsicLiouville.Nondegenerate
      (IntrinsicLiouville.exteriorDerivative α) x)
    (hout : ∀ b : IntrinsicBoundary.Point k M,
      0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ)
        (IntrinsicLiouville.normalDefiningFunction (IntrinsicBoundary.chartAt b).ambient) b.val
          (IntrinsicLiouville.liouvilleVector α (IntrinsicLiouville.exteriorDerivative α) b.val)))
    (hode : ∀ b, IsMIntegralCurveOn (fun t => C (t, b))
      (fun x => -IntrinsicLiouville.liouvilleVector α
        (IntrinsicLiouville.exteriorDerivative α) x) (Ico 0 δ))
    {f : M → ℝ} (hf : IntrinsicLiouville.IsLocallyExtendibleScalar (k := k) f) :
    ∃ g : (extensionManifold hδ C hemb hC hboundary hinv hzero).Point → ℝ,
      ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ g ∧
      ∀ x, g (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x) = f x := by
  apply exists_scalarExtension_of_collar_germs hδ C hemb hC hboundary hinv hzero
    (IntrinsicLiouville.contMDiff_of_isLocallyExtendibleScalar hf)
  intro b
  have hx : b.val ∈ (IntrinsicBoundary.chartAt b).ambient.source := by
    have h := IntrinsicBoundary.mem_chartAt_source b
    rwa [(IntrinsicBoundary.chartAt b).source_eq] at h
  exact IntrinsicLiouville.exists_seam_scalar_germ_of_primitive α hα hnd b (hout b)
    C hδ hzero hode f
    (hf (IntrinsicBoundary.chartAt b).ambient (IntrinsicBoundary.chartAt b).mem_atlas b.val hx)

end FsFltz.Geometry.IntrinsicCollarGluing

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Source primitive and outwardness data select a single actual compact
domain presentation with its native carrier diffeomorphism before any additional
scalar is chosen. The primitive
and every locally extendible scalar are then extended on that same
boundaryless manifold with exact preservation on the whole source.
This finite foundation result asserts no completion or comparison chain. -/
theorem exists_compactDomain_with_native_primitive_and_scalar_extensions
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hout : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
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
      range i = D.carrier ∧ frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M ∧
      D.extension.IsSmoothForm lam ∧
      (fun x => (lam (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α ∧
      ∀ f : M → ℝ, IsLocallyExtendibleScalar (k := k) f →
        ∃ g : D.extension.Point → ℝ,
          ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ g ∧ ∀ x, g (i x) = f x := by
  obtain ⟨C, δ, hδ, hC, hemb, hzero, hode, hboundary, hinv, _, _⟩ :=
    exists_topological_extension_with_primitive_collar α hα hnd hout
  let c : IntrinsicCollarGluing.Half δ (IntrinsicBoundary.Point k M) → M := fun p => C p.val
  have hb : ∀ p : IntrinsicCollarGluing.Half δ (IntrinsicBoundary.Point k M),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C p.val) ↔ p.val.1 = 0 :=
    fun p => hboundary p.val.2 p.val.1 p.property.1
  let D := IntrinsicCollarGluing.compactDomain hδ C hemb hC hb hinv hzero
  let i : M → D.extension.Point := IntrinsicCollarGluing.original c
  let lam : D.extension.Form 1 :=
    IntrinsicCollarGluing.gluedPrimitive hδ C hemb hC hb hinv hzero α
  have hZ := contraction_liouvilleVector α (exteriorDerivative α) hnd
  refine ⟨D, i, lam,
    IntrinsicCollarGluing.originalDiffeomorph hδ C hemb hC hb hinv hzero, fun _ => rfl,
    IntrinsicCollarGluing.contMDiff_original hδ C hemb hC hb hinv hzero,
    IntrinsicCollarGluing.isClosedEmbedding_original hδ c hemb,
    IntrinsicCollarGluing.bijective_mfderiv_original hδ C hemb hC hb hinv hzero,
    rfl, IntrinsicCollarGluing.frontier_range_original hδ c hemb hb hzero,
    IntrinsicCollarGluing.isSmoothForm_gluedPrimitive hδ C hemb hC hb hinv hzero
      α hα (liouvilleVector α (exteriorDerivative α)) hZ hode,
    IntrinsicCollarGluing.pullback_gluedPrimitive_original hδ C hemb hC hb hinv hzero
      α hα (liouvilleVector α (exteriorDerivative α)) hZ hode, ?_⟩
  have houtnorm (b : IntrinsicBoundary.Point k M) :
      0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ)
        (normalDefiningFunction (IntrinsicBoundary.chartAt b).ambient) b.val
          (liouvilleVector α (exteriorDerivative α) b.val)) := by
    obtain ⟨rho, beta, hz, hs, hr, hbeta, heq, hp⟩ := hout b
    have hx : b.val ∈ (IntrinsicBoundary.chartAt b).ambient.source := by
      have h := IntrinsicBoundary.mem_chartAt_source b
      rwa [(IntrinsicBoundary.chartAt b).source_eq] at h
    have hn := (outward_iff_negative_normal_of_localDefiningFunction
      (IntrinsicBoundary.chartAt b).mem_atlas hx b.property rho hz hs hr hbeta heq
      (liouvilleVector α (exteriorDerivative α) b.val)).mp hp
    rw [normalDefiningFunction_derivative (IntrinsicBoundary.chartAt b).mem_atlas hx]
    exact neg_pos.mpr hn
  intro f hf
  exact IntrinsicCollarGluing.exists_scalarExtension_of_primitive_collar
    hδ C hemb hC hb hinv hzero α hα hnd houtnorm hode hf


/-- Forgetting the native carrier diffeomorphism retains the original scalar
extension API, with the same domain chosen before the scalar. -/
theorem exists_compactDomain_with_primitive_and_scalar_extensions
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hout : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector α (exteriorDerivative α) x.val))) :
    ∃ (D : CompactDomain (k + 1)) (i : M → D.extension.Point) (lam : D.extension.Form 1),
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i ∧
      Topology.IsClosedEmbedding i ∧
      (∀ x, Function.Bijective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) ∧
      range i = D.carrier ∧ frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M ∧
      D.extension.IsSmoothForm lam ∧
      (fun x => (lam (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α ∧
      ∀ f : M → ℝ, IsLocallyExtendibleScalar (k := k) f →
        ∃ g : D.extension.Point → ℝ,
          ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ g ∧ ∀ x, g (i x) = f x := by
  obtain ⟨D, i, lam, e, _, hi, hemb, hbij, hrange, hfrontier, hlam, hpull, hscalar⟩ :=
    exists_compactDomain_with_native_primitive_and_scalar_extensions α hα hnd hout
  exact ⟨D, i, lam, hi, hemb, hbij, hrange, hfrontier, hlam, hpull, hscalar⟩

end FsFltz.Geometry.IntrinsicLiouville
