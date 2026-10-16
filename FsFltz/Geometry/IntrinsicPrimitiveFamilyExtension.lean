import FsFltz.Geometry.IntrinsicScalarExtension
import FsFltz.Geometry.CompletionFamily
import FsFltz.Geometry.IntrinsicFormFamilyGluing

/-!
# Joint native primitive extension on a fixed collar presentation

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and
`sec:lean`, lines 788–814. The reference primitive chooses one spatial
collar. Additional primitive families use their joint coordinate germs on
that same spatial presentation; no slice-wise choice of carrier is made.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Joint open coefficient germs, including the parameter endpoints and
the spatial boundary. Only agreement at actual source parameters is required. -/
def IsLocallyExtendibleFormFamily {r : ℕ} (α : Parameter → Form k M r) : Prop :=
  ∀ e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)),
    e ∈ atlas (EuclideanHalfSpace (k + 1)) M → ∀ t : Parameter, ∀ x ∈ e.source,
      ∃ (U : Set (ℝ × Model (k + 1)))
        (β : ℝ × Model (k + 1) → Model (k + 1) [⋀^Fin r]→L[ℝ] ℝ),
        IsOpen U ∧ (t.val, e.extend (𝓡∂ (k + 1)) x) ∈ U ∧
        ContDiffOn ℝ ∞ β U ∧
        ∀ s : Parameter, ∀ y ∈ (e.extend (𝓡∂ (k + 1))).target,
          (s.val, y) ∈ U → β (s.val, y) = formInChart e (α s) y

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Every slice of joint source germs is locally extendible, with no
additional regularity or geometric inequalities outside the interval. -/
theorem IsLocallyExtendibleFormFamily.slice {r : ℕ}
    {α : Parameter → Form k M r} (hα : IsLocallyExtendibleFormFamily α)
    (t : Parameter) : IsLocallyExtendibleForm (α t) := by
  intro e he x hx
  obtain ⟨U, β, hU, hpU, hβ, heq⟩ := hα e he t x hx
  let q : Model (k + 1) → ℝ × Model (k + 1) := fun y => (t.val, y)
  refine ⟨β ∘ q, q ⁻¹' U, hU.preimage (continuous_const.prodMk continuous_id), hpU,
    hβ.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hy => hy), ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds ((hU.preimage (continuous_const.prodMk continuous_id)).mem_nhds hpU)]
    with y hy hyU
  exact heq t y hy hyU

end FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicCollarGluing

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
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

local instance primitiveFamilyBandChartedSpace :
    ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ
local instance primitiveFamilyBandIsManifold :
    IsManifold 𝓘(ℝ, Model (k + 1)) ∞ (Band δ (IntrinsicBoundary.Point k M)) :=
  band_isManifold δ

/-- An actual source chart acquires a smooth coordinate extension on the
fixed collar quotient near each native boundary point. Agreement holds for
every original point in that neighborhood, not just at the seam. -/
theorem exists_boundary_coordinate_extension_of_primitive
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (hnd : ∀ z, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative α) z)
    (x : IntrinsicBoundary.Point k M)
    (hout : 0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ)
      (IntrinsicLiouville.normalDefiningFunction (IntrinsicBoundary.chartAt x).ambient) x.val
        (IntrinsicLiouville.liouvilleVector α (IntrinsicLiouville.exteriorDerivative α) x.val)))
    (hode : ∀ b, IsMIntegralCurveOn (fun t => C (t, b))
      (fun z => -IntrinsicLiouville.liouvilleVector α
        (IntrinsicLiouville.exteriorDerivative α) z) (Ico 0 δ)) :
    ∃ (O : Set (extensionManifold hδ C hemb hC hboundary hinv hzero).Point)
      (Q : (extensionManifold hδ C hemb hC hboundary hinv hzero).Point → Model (k + 1)),
      IsOpen O ∧ original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) x.val ∈ O ∧
      ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ Q O ∧
      ∀ y, original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) y ∈ O →
        y ∈ (IntrinsicBoundary.chartAt x).ambient.source ∧
        Q (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) y) =
          (IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) y := by
  let c := IntrinsicBoundary.chartAt x
  have hx : x ∈ c.chart.source := IntrinsicBoundary.mem_chartAt_source x
  have hex : x.val ∈ c.ambient.source := by
    have h := hx
    rwa [c.source_eq] at h
  obtain ⟨g, V, ε, hg, hV, hxV, _, hε, _, hgzero, _, _, _, hmatch⟩ :=
    IntrinsicCollar.exists_seam_coordinate_germ_of_scalar_extensions c hx
      (fun z => -IntrinsicLiouville.liouvilleVector α
        (IntrinsicLiouville.exteriorDerivative α) z) C hδ hzero hode
      (IntrinsicLiouville.inward_liouvilleVector_scalar_extensions_of_primitive α hα hnd
        c.ambient c.mem_atlas x.val hex)
      (IntrinsicLiouville.inward_of_normalDefiningFunction_outward c.mem_atlas hex
        (IntrinsicLiouville.liouvilleVector α (IntrinsicLiouville.exteriorDerivative α)) hout)
  let X := extensionManifold hδ C hemb hC hboundary hinv hzero
  let := extensionChartedSpace hδ C hemb hboundary hzero
  let := extension_isManifold hδ C hemb hC hboundary hinv hzero
  let C₀ := fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val
  let i := original C₀
  let p : Band δ (IntrinsicBoundary.Point k M) := boundaryIntoBand hδ x
  let v := cylinderInverse hδ C₀ hemb p
  let Y := c.chart.source ∩ c.chart ⁻¹' V
  have hc : ContMDiffOn 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) ∞ c.chart c.chart.source :=
    contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas ⟨c, rfl⟩)
  have hY : IsOpen Y := hc.continuousOn.isOpen_inter_preimage c.chart.open_source hV
  let S := Ioo (-ε) ε ×ˢ Y
  have hS : IsOpen S := isOpen_Ioo.prod hY
  let O := range (cylinder C₀) ∩ (Subtype.val ∘ v) ⁻¹' S
  let Q : X.Point → Model (k + 1) := fun z => g ((v z).val.1, c.chart (v z).val.2)
  have hv := contMDiffOn_cylinderInverse hδ C hemb hC hboundary hinv hzero p
  have hcv := (contMDiff_band_val δ).comp_contMDiffOn hv
  have hO : IsOpen O := hcv.continuousOn.isOpen_inter_preimage
    (isOpenEmbedding_cylinder hδ C₀ hemb).isOpen_range hS
  have hp : cylinder C₀ p = i x.val := boundaryInclusion_map hδ C hemb hC hboundary hinv hzero x
  have hxO : i x.val ∈ O := by
    refine ⟨⟨p, hp⟩, ?_⟩
    change (cylinderInverse hδ C₀ hemb p (i x.val)).val ∈ S
    rw [← hp, cylinderInverse_cylinder]
    change (0, x) ∈ S
    exact ⟨⟨by linarith, hε⟩, hx, hxV⟩
  have hQ : ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ Q O := by
    have hcvO : ContMDiffOn 𝓘(ℝ, Model (k + 1))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ (Subtype.val ∘ v) O :=
      hcv.mono inter_subset_left
    have ht := (contMDiff_fst.comp_contMDiffOn hcvO)
    have hb := hc.comp
      (contMDiff_snd.comp_contMDiffOn hcvO)
      (fun z hz => hz.2.2.1)
    exact hg.contMDiff.comp_contMDiffOn (ht.prodMk_space hb)
  refine ⟨O, Q, hO, hxO, hQ, ?_⟩
  intro y hy
  have hrel : i y = cylinder C₀ (v (i y)) :=
    (cylinder_cylinderInverse hδ C₀ hemb p hy.1).symm
  obtain ⟨ht, hCy⟩ := (original_eq_cylinder_iff C₀ y (v (i y))).mp hrel
  change C (v (i y)).val = y at hCy
  have hb : (v (i y)).val.2 ∈ Y := hy.2.2
  have htime : (v (i y)).val.1 ∈ Ico 0 ε := ⟨ht, hy.2.1.2⟩
  obtain ⟨hsource, hcoord⟩ := hmatch (c.chart (v (i y)).val.2) hb.2
    (v (i y)).val.1 htime
  rw [c.chart.left_inv hb.1, hCy] at hsource hcoord
  exact ⟨hsource, hcoord.symm⟩

/-- Interior coordinate extension on the same quotient, using the actual
open interior attachment and its produced smooth inverse. -/
theorem exists_interior_coordinate_extension (x : IntrinsicInterior.Point k M) :
    ∃ (O : Set (extensionManifold hδ C hemb hC hboundary hinv hzero).Point)
      (Q : (extensionManifold hδ C hemb hC hboundary hinv hzero).Point → Model (k + 1)),
      IsOpen O ∧ original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) x.val ∈ O ∧
      ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ Q O ∧
      ∀ y, original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) y ∈ O →
        y ∈ (chartAt (EuclideanHalfSpace (k + 1)) x.val).source ∧
        Q (original (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) y) =
          (chartAt (EuclideanHalfSpace (k + 1)) x.val).extend (𝓡∂ (k + 1)) y := by
  let X := extensionManifold hδ C hemb hC hboundary hinv hzero
  let := extensionChartedSpace hδ C hemb hboundary hzero
  let := extension_isManifold hδ C hemb hC hboundary hinv hzero
  let C₀ := fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val
  let i := original C₀
  let j := interiorIn C₀
  have hj := isOpenEmbedding_interiorIn hδ C₀ hemb hboundary
  let : Nonempty (IntrinsicInterior.Point k M) := ⟨x⟩
  let v : X.Point → IntrinsicInterior.Point k M := (hj.toOpenPartialHomeomorph j).symm
  have hv : ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ v (range j) := by
    rintro z ⟨u, rfl⟩
    have ha : (chartAt (Model (k + 1)) u).lift_openEmbedding hj ∈
        IsManifold.maximalAtlas 𝓘(ℝ, Model (k + 1)) ∞ X.Point := by
      apply IsManifold.subset_maximalAtlas
      exact Or.inl ⟨chartAt (Model (k + 1)) u, chart_mem_atlas _ u, rfl⟩
    obtain ⟨g, hg, _, heq⟩ := smooth_inverse_germ_of_lifted_chart hj u ha
    apply (hg.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [heq] with z hz
    exact (congrArg v hz).symm.trans (hj.toOpenPartialHomeomorph_left_inv j)
  let e := chartAt (EuclideanHalfSpace (k + 1)) x.val
  let O := range j ∩ (Subtype.val ∘ v) ⁻¹' e.source
  have hvval := IntrinsicInterior.contMDiff_val.comp_contMDiffOn hv
  have hO : IsOpen O := hvval.continuousOn.isOpen_inter_preimage hj.isOpen_range e.open_source
  have hvi : v (j x) = x := hj.toOpenPartialHomeomorph_left_inv j
  have hxO : i x.val ∈ O := by
    change j x ∈ O
    refine ⟨mem_range_self x, ?_⟩
    change (v (j x)).val ∈ e.source
    rw [hvi]
    exact mem_chart_source (EuclideanHalfSpace (k + 1)) x.val
  let Q : X.Point → Model (k + 1) := e.extend (𝓡∂ (k + 1)) ∘ Subtype.val ∘ v
  have hQ : ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ Q O :=
    e.contMDiffOn_extend (IsManifold.subset_maximalAtlas
      (I := 𝓡∂ (k + 1)) (n := ∞) (chart_mem_atlas (EuclideanHalfSpace (k + 1)) x.val)) |>.comp
      (hvval.mono inter_subset_left) (fun _ hz => hz.2)
  refine ⟨O, Q, hO, hxO, hQ, ?_⟩
  intro y hy
  obtain ⟨u, hu⟩ := hy.1
  have huy : u.val = y := (isClosedEmbedding_original hδ C₀ hemb).injective hu
  have hvy : v (i y) = u := by
    exact (congrArg v hu).symm.trans (hj.toOpenPartialHomeomorph_left_inv j)
  have hsource : y ∈ e.source := by
    have h := hy.2
    change (v (i y)).val ∈ e.source at h
    simpa only [hvy, huy] using h
  exact ⟨hsource, by change e.extend (𝓡∂ (k + 1)) (v (i y)).val = _; rw [hvy, huy]⟩

end FsFltz.Geometry.IntrinsicCollarGluing

namespace FsFltz.Geometry.SmoothManifold

/-- Actual spatial pullback of a joint coefficient germ through one fixed
locally smooth coordinate map is jointly smooth on its actual open domain. -/
theorem isSmoothFormFamilyOn_modelPullback {d m : ℕ} (N : SmoothManifold d)
    (Q : N.Point → Model m) {O : Set N.Point} (hO : IsOpen O)
    (hQ : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model m) ∞ Q O)
    (β : ℝ × Model m → Model m [⋀^Fin 1]→L[ℝ] ℝ)
    {U : Set (ℝ × Model m)} (hU : IsOpen U) (hβ : ContDiffOn ℝ ∞ β U) :
    N.IsSmoothFormFamilyOn
      (fun s z => (β (s, Q z)).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model m) Q z))
      ((univ ×ˢ O) ∩ (fun p : ℝ × N.Point => (p.1, Q p.2)) ⁻¹' U) := by
  intro a p hp
  let c := chartAt (Model d) a
  let W := c.target ∩ c.symm ⁻¹' O
  have hW : IsOpen W := c.continuousOn_symm.isOpen_inter_preimage c.open_target hO
  let g := Q ∘ c.symm
  have hg : ContDiffOn ℝ ∞ g W :=
    (hQ.comp ((contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := a)).mono inter_subset_left)
      (fun _ hz => hz.2)).contDiffOn
  have hpW : p.2 ∈ W := ⟨hp.1.2, hp.2.1.2⟩
  have hgat : ContDiffAt ℝ ∞ g p.2 := hg.contDiffAt (hW.mem_nhds hpW)
  have hgder : ContDiffAt ℝ ∞ (fun q : ℝ × Model d => fderiv ℝ g q.2) p :=
    (hg.fderiv_of_isOpen (m := ∞) hW (by simp) p.2 hpW).contDiffAt
      (hW.mem_nhds hpW) |>.comp p contDiffAt_snd
  have hb : ContDiffAt ℝ ∞ (fun q : ℝ × Model d => β (q.1, g q.2)) p :=
    (hβ.contDiffAt (hU.mem_nhds hp.2.2)).comp p
      (contDiffAt_fst.prodMk (hgat.comp p contDiffAt_snd))
  have hs := contDiffAt_oneForm_comp _ _ p hb hgder
  apply (hs.congr_of_eventuallyEq ?_).contDiffWithinAt
  have hQg : ∀ᶠ y in 𝓝 p.2, y ∈ W := hW.mem_nhds hpW
  filter_upwards [continuous_snd.continuousAt.eventually hQg] with q hq
  have hQc := ((hQ.contMDiffAt (hO.mem_nhds hq.2)).mdifferentiableAt (by simp))
  have hc := (mdifferentiable_chart (I := 𝓘(ℝ, Model d)) a).mdifferentiableAt_symm hq.1
  have hd := mfderiv_comp q.2 hQc hc
  rw [mfderiv_eq_fderiv] at hd
  unfold formInChart
  ext vs
  change β (q.1, Q (c.symm q.2)) (fun j =>
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model m) Q (c.symm q.2)
        (N.inverseChartTangentMap a q.2 (vs j))) =
    β (q.1, g q.2) (fun j => fderiv ℝ g q.2 (vs j))
  rw [hd]
  rfl

end FsFltz.Geometry.SmoothManifold
