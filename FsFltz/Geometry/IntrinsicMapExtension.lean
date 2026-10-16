import FsFltz.Geometry.IntrinsicScalarExtension
import FsFltz.Geometry.SmoothMapFiniteExtension
import FsFltz.Geometry.IntrinsicMapSeam

/-!
# Manifold-valued maps on the same native collar presentation

Source: `geoemtric-part-fsf.tex`, conventions 119–122, `def:pair`,
132–146, `def:chain`, 163–169, and `sec:lean`, 788–814.
Source map smoothness includes actual open coordinate extension germs.
Finite target-chart patching produces a map on a neighborhood of the
compact original carrier, with its original values preserved exactly.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {F N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace N] [ChartedSpace F N]

/-- Across-boundary source smoothness for a manifold-valued map. The map
is continuous, and every source chart has an actual open smooth extension
of its coordinates in the target chart at the source value. Continuity
also guarantees containment in that target chart near the source point. -/
def IsLocallyExtendibleMap (f : M → N) : Prop :=
  Continuous f ∧
  ∀ e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)),
    e ∈ atlas (EuclideanHalfSpace (k + 1)) M → ∀ x ∈ e.source,
      ∃ (β : Model (k + 1) → F) (U : Set (Model (k + 1))),
        IsOpen U ∧ e.extend (𝓡∂ (k + 1)) x ∈ U ∧ ContDiffOn ℝ ∞ β U ∧
        β =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target]
          (e.extend (𝓡∂ (k + 1)) x)]
          (fun z => chartAt F (f x) (f ((e.extend (𝓡∂ (k + 1))).symm z)))

/-- Actual source chart extension germs imply native manifold smoothness;
the continuity field is used to satisfy the manifold chart criterion. -/
theorem contMDiff_of_isLocallyExtendibleMap {f : M → N}
    (hf : IsLocallyExtendibleMap (k := k) (F := F) f) :
    ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, F) ∞ f := by
  intro x
  let e := chartAt (EuclideanHalfSpace (k + 1)) x
  have hx : x ∈ e.source := mem_chart_source _ _
  obtain ⟨β, U, hU, hxU, hβ, heq⟩ := hf.2 e (chart_mem_atlas _ x) x hx
  have ht : e.extend (𝓡∂ (k + 1)) x ∈ (e.extend (𝓡∂ (k + 1))).target :=
    (e.extend (𝓡∂ (k + 1))).map_source (by simpa only [e.extend_source] using hx)
  have heqpoint := heq.eq_of_nhdsWithin ht
  rw [e.nhdsWithin_extend_target_eq hx] at heq
  apply contMDiffAt_iff.mpr
  refine ⟨hf.1.continuousAt, ?_⟩
  have H := (hβ.contDiffAt (hU.mem_nhds hxU)).contDiffWithinAt.congr_of_eventuallyEq
    heq.symm heqpoint.symm
  simpa only [extChartAt, e, OpenPartialHomeomorph.extend_coe, Function.comp_def,
    modelWithCornersSelf_coe, Function.id_def] using H

end FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicCollarGluing

private theorem exists_map_on_open_patch
    {E F U X N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace U] [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace E U] [ChartedSpace E X] [ChartedSpace F N]
    [IsManifold 𝓘(ℝ, E) ∞ U] [IsManifold 𝓘(ℝ, E) ∞ X]
    {i : U → X} (hi : IsOpenEmbedding i) (u : U)
    (hatlas : ∀ q : U, (chartAt E q).lift_openEmbedding hi ∈
      IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ X)
    {f : U → N} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    ∃ (O : TopologicalSpace.Opens X) (_hO : (O : Set X) = range i)
      (g : O → N), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g ∧
      ∀ q (hq : i q ∈ O), g ⟨i q, hq⟩ = f q := by
  let : Nonempty U := ⟨u⟩
  let inv : X → U := (hi.toOpenPartialHomeomorph i).symm
  have hinv : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ inv (range i) := by
    rintro z ⟨q, rfl⟩
    obtain ⟨g, hg, _, heq⟩ := smooth_inverse_germ_of_lifted_chart hi q (hatlas q)
    apply (hg.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [heq] with z hz
    exact (congrArg inv hz).symm.trans (hi.toOpenPartialHomeomorph_left_inv i)
  let O : TopologicalSpace.Opens X := ⟨range i, hi.isOpen_range⟩
  let g : O → N := fun z => f (inv z.val)
  have hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun z : O => inv z.val) := by
    intro z
    exact ((hinv.contMDiffAt (hi.isOpen_range.mem_nhds z.property)).comp
      z contMDiff_subtype_val.contMDiffAt)
  refine ⟨O, rfl, g, hf.comp hv, ?_⟩
  intro q hq
  exact congrArg f (hi.toOpenPartialHomeomorph_left_inv i)

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M]
  {F N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
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

/-- Smooth native interior data and actual two-sided seam map germs give
one coherent partial map around the whole compact original carrier on the
same constructed collar quotient. The germs may disagree off the carrier. -/
theorem exists_mapExtension_of_collar_germs
    {f : M → N} (hf : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, F) ∞ f)
    (hseam : ∀ b : IntrinsicBoundary.Point k M,
      ∃ W : TopologicalSpace.Opens (ℝ × IntrinsicBoundary.Point k M),
        (0, b) ∈ W ∧ ∃ a : W → N,
          ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) 𝓘(ℝ, F) ∞ a ∧
          ∀ p : W, p.val ∈ Half δ (IntrinsicBoundary.Point k M) → a p = f (C p.val)) :
    ∃ W : TopologicalSpace.Opens
        (extensionManifold hδ C hemb hC hboundary hinv hzero).Point,
      range (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) ⊆
        (W : Set (extensionManifold hδ C hemb hC hboundary hinv hzero).Point) ∧
      ∃ g : W → N, ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, F) ∞ g ∧
        ∀ x (hx : original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x ∈ W),
          g ⟨original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x, hx⟩ = f x := by
  classical
  let C₀ := fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val
  let i := original C₀
  let := extensionChartedSpace hδ C hemb hboundary hzero
  let := extension_isManifold hδ C hemb hC hboundary hinv hzero
  let : T2Space (Extension C₀) := t2Space_extension hδ C₀ hemb
  let : SecondCountableTopology (Extension C₀) :=
    secondCountableTopology_extension hδ C₀ hemb hboundary hzero
  let f₀ : range i → N := fun z => f z.property.choose
  have hFi (x : M) (hx : i x ∈ range i) : f₀ ⟨i x, hx⟩ = f x := by
    exact congrArg f ((isClosedEmbedding_original hδ C₀ hemb).injective hx.choose_spec)
  have hlocal : ∀ z : range i, ∃ O : TopologicalSpace.Opens (Extension C₀),
      z.val ∈ O ∧ ∃ g : O → N,
        ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, F) ∞ g ∧
        ∀ y (hyO : y ∈ O) (hyA : y ∈ range i), g ⟨y, hyO⟩ = f₀ ⟨y, hyA⟩ := by
    rintro ⟨z, x, rfl⟩
    rcases (𝓡∂ (k + 1)).isInteriorPoint_or_isBoundaryPoint x with hx | hx
    · let u : IntrinsicInterior.Point k M := ⟨x, hx⟩
      let j := interiorIn C₀
      have hj := isOpenEmbedding_interiorIn hδ C₀ hemb hboundary
      have ha (q : IntrinsicInterior.Point k M) :
          (chartAt (Model (k + 1)) q).lift_openEmbedding hj ∈
            IsManifold.maximalAtlas 𝓘(ℝ, Model (k + 1)) ∞ (Extension C₀) := by
        apply IsManifold.subset_maximalAtlas
        exact Or.inl ⟨chartAt (Model (k + 1)) q, chart_mem_atlas _ q, rfl⟩
      obtain ⟨O, hO, g, hg, heq⟩ := exists_map_on_open_patch hj u ha
        (hf.comp IntrinsicInterior.contMDiff_val)
      have hxO : i x ∈ O := by
        change i x ∈ (O : Set (Extension C₀))
        rw [hO]
        exact mem_range_self u
      refine ⟨O, hxO, g, hg, ?_⟩
      intro z hzO hzA
      obtain ⟨q, hq⟩ := show z ∈ range j by rwa [← hO]
      have he : g ⟨z, hzO⟩ = f q.val := by
        subst z
        exact heq q hzO
      have hfi : f₀ ⟨z, hzA⟩ = f q.val := by
        subst z
        exact hFi q.val hzA
      exact he.trans hfi.symm
    · let b : IntrinsicBoundary.Point k M := ⟨x, hx⟩
      let p : Band δ (IntrinsicBoundary.Point k M) :=
        ⟨(0, b), ⟨by linarith, hδ⟩, mem_univ _⟩
      let j := cylinder C₀
      let v := cylinderInverse hδ C₀ hemb p
      have hp : j p = i x := by
        symm
        exact (original_eq_cylinder_iff C₀ x p).mpr ⟨le_rfl, hzero b⟩
      obtain ⟨W, hpW, a, ha, heq⟩ := hseam b
      have hv := contMDiffOn_cylinderInverse hδ C hemb hC hboundary hinv hzero p
      have hj := isOpenEmbedding_cylinder hδ C₀ hemb
      let O : TopologicalSpace.Opens (Extension C₀) :=
        ⟨range j ∩ (Subtype.val ∘ v) ⁻¹' W,
          ((contMDiff_band_val δ).comp_contMDiffOn hv).continuousOn.isOpen_inter_preimage
            hj.isOpen_range W.isOpen⟩
      have hxO : i x ∈ O := by
        rw [← hp]
        refine ⟨mem_range_self p, ?_⟩
        change (cylinderInverse hδ C₀ hemb p (cylinder C₀ p)).val ∈ W
        rw [cylinderInverse_cylinder]
        exact hpW
      let w : O → W := fun z => ⟨(v z.val).val, z.property.2⟩
      have hvO : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
          (fun z : O => v z.val) := by
        intro z
        exact (hv.contMDiffAt (hj.isOpen_range.mem_nhds z.property.1)).comp
          z contMDiff_subtype_val.contMDiffAt
      have hw : ContMDiff 𝓘(ℝ, Model (k + 1))
          (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ w :=
        (ContMDiff.subtypeVal_comp_iff W w).mp ((contMDiff_band_val δ).comp hvO)
      refine ⟨O, hxO, a ∘ w, ha.comp hw, ?_⟩
      intro z hzO hzA
      obtain ⟨y, rfl⟩ := hzA
      have hyj : i y = j (v (i y)) :=
        (cylinder_cylinderInverse hδ C₀ hemb p hzO.1).symm
      obtain ⟨ht, hCy⟩ := (original_eq_cylinder_iff C₀ y (v (i y))).mp hyj
      have hhalf : (v (i y)).val ∈ Half δ (IntrinsicBoundary.Point k M) :=
        ⟨⟨ht, (v (i y)).property.1.2⟩, mem_univ _⟩
      exact (heq (w ⟨i y, hzO⟩) hhalf).trans
        ((congrArg f hCy).trans (hFi y (mem_range_self y)).symm)
  have hcompact : IsCompact (range i) :=
    isCompact_univ.image (isClosedEmbedding_original hδ C₀ hemb).continuous |>
      (by simpa only [image_univ] using ·)
  obtain ⟨W, hW, g, hg, heq⟩ :=
    SmoothMapExtension.exists_smoothMapExtension_of_compact hcompact f₀ hlocal
  exact ⟨W, hW, g, hg, fun x hx => (heq (i x) hx (mem_range_self x)).trans
    (hFi x (mem_range_self x))⟩

/-- Source primitive and source map chart extensions construct a coherent
smooth map around the compact original carrier of this very same collar
quotient. The target chart may vary throughout the carrier. No ambient map
or compatible collection of off-carrier germs is supplied. -/
theorem exists_mapExtension_of_primitive_collar
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
    {f : M → N}
    (hf : IntrinsicLiouville.IsLocallyExtendibleMap (k := k) (F := F) f) :
    ∃ W : TopologicalSpace.Opens
        (extensionManifold hδ C hemb hC hboundary hinv hzero).Point,
      range (original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) ⊆
        (W : Set (extensionManifold hδ C hemb hC hboundary hinv hzero).Point) ∧
      ∃ g : W → N, ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, F) ∞ g ∧
        ∀ x (hx : original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x ∈ W),
          g ⟨original (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x, hx⟩ = f x := by
  apply exists_mapExtension_of_collar_germs hδ C hemb hC hboundary hinv hzero
    (IntrinsicLiouville.contMDiff_of_isLocallyExtendibleMap hf)
  intro b
  have hx : b.val ∈ (IntrinsicBoundary.chartAt b).ambient.source := by
    have h := IntrinsicBoundary.mem_chartAt_source b
    rwa [(IntrinsicBoundary.chartAt b).source_eq] at h
  exact IntrinsicLiouville.exists_seam_map_germ_of_primitive α hα hnd b (hout b)
    C hδ hzero hode hC f hf.1
    (hf.2 (IntrinsicBoundary.chartAt b).ambient (IntrinsicBoundary.chartAt b).mem_atlas b.val hx)

end FsFltz.Geometry.IntrinsicCollarGluing
