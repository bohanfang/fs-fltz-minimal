import FsFltz.Geometry.IntrinsicBundleBoundaryTransport
import FsFltz.Geometry.IntrinsicBundleNativeData
import FsFltz.Geometry.IntrinsicInterior

/-!
# Real germs of original compact transitions on the native interior

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`def:maslov`, lines 225–232; and `sec:lean`, lines 788–814.
The actual joint coordinate germs of a compact bundle transition restrict
to target-valued real germs on its boundaryless native interior. In particular,
the real parameter remains free near either interval endpoint. Native
`ContMDiff` regularity is not used as a substitute for these extension germs.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle Topology

namespace FsFltz.Geometry.IntrinsicInterior

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- An arbitrary original native chart restricts to a Euclidean interior
chart, retaining its actual ambient coordinate map. -/
theorem exists_chart_from_atlas
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)))
    (he : e ∈ _root_.atlas (EuclideanHalfSpace (k + 1)) M)
    (x : Point k M) (hx : x.val ∈ e.source) :
    ∃ c : Chart k M, c.ambient = e ∧ x ∈ c.chart.source := by
  have himage : e.IsImage ((𝓡∂ (k + 1)).interior M)
      {v : EuclideanHalfSpace (k + 1) | 0 < v.val 0} := by
    intro y hy
    exact (isInteriorPoint_iff_chart_pos he hy).symm
  let z : {v : EuclideanHalfSpace (k + 1) // 0 < v.val 0} :=
    (positiveHalfSpaceHomeomorph k).symm (Classical.choice (positiveModel_nonempty k))
  obtain ⟨r, hrs, hrt, hrf, hrg⟩ := exists_openPartialHomeomorph_subtypes e himage x z
  let q := r.trans (positiveHalfSpaceChart k)
  refine ⟨⟨e, he, q, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · change r.source ∩ r ⁻¹' (positiveHalfSpaceChart k).source = _
    rw [positiveHalfSpaceChart_source, preimage_univ, inter_univ]
    exact hrs
  · ext v
    change v ∈ (positiveHalfSpaceChart k).target ∧
      (positiveHalfSpaceChart k).symm v ∈ r.target ↔ _
    rw [positiveHalfSpaceChart_target, hrt]
    exact ⟨fun h => ⟨h.1, by simpa [positiveHalfSpaceChart_symm_val h.1] using h.2⟩,
      fun h => ⟨h.1, by simpa [positiveHalfSpaceChart_symm_val h.1] using h.2⟩⟩
  · intro y hy
    change (r y).val.val = (e y.val).val
    rw [hrf y hy.1]
  · intro v hv
    change (r.symm ((positiveHalfSpaceChart k).symm v)).val = _
    rw [hrg _ hv.2]
    exact congrArg e.symm (positiveHalfSpaceChart_symm_val (by simpa using hv.1))
  · change x ∈ r.source ∩ r ⁻¹' (positiveHalfSpaceChart k).source
    rw [hrs, positiveHalfSpaceChart_source]
    exact ⟨hx, mem_univ _⟩

end FsFltz.Geometry.IntrinsicInterior

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The literal interior restriction on the actual parameter set. -/
def interiorFamilyOn (S : Set Parameter) (f : Parameter → M → M)
    (hi : ∀ t ∈ S, ∀ x : IntrinsicInterior.Point k M,
      (𝓡∂ (k + 1)).IsInteriorPoint (f t x.val)) :
    Parameter → IntrinsicInterior.Point k M → IntrinsicInterior.Point k M := by
  classical
  exact fun t x => if h : t ∈ S then ⟨f t x.val, hi t h x⟩ else x

omit [T2Space M] [SecondCountableTopology M] [IsManifold (𝓡∂ (k + 1)) ∞ M] in
@[simp] theorem interiorFamilyOn_val {S : Set Parameter} {f : Parameter → M → M}
    (hi : ∀ t ∈ S, ∀ x : IntrinsicInterior.Point k M,
      (𝓡∂ (k + 1)).IsInteriorPoint (f t x.val)) {t : Parameter} (ht : t ∈ S)
    (x : IntrinsicInterior.Point k M) :
    (interiorFamilyOn S f hi t x).val = f t x.val := by
  simp only [interiorFamilyOn, dite_eq_left ht]

/-- Restriction of the supplied joint open coordinate germs gives actual
interior-valued real germs. The target chart's open interior ensures that
the off-interval extension takes values in the same native interior. -/
theorem HasSmoothFamilyOn.interiorRestriction {S : Set Parameter} (hS : IsOpen S)
    {f : Parameter → M → M} (hf : HasSmoothFamilyOn (𝓡∂ (k + 1)) S f)
    (hfc : ContinuousOn (fun p : Parameter × M => f p.1 p.2) (S ×ˢ univ))
    (hi : ∀ t ∈ S, ∀ x : IntrinsicInterior.Point k M,
      (𝓡∂ (k + 1)).IsInteriorPoint (f t x.val)) :
    HasSmoothTargetFamilyOn 𝓘(ℝ, Model (k + 1))
      (IntrinsicInterior.smoothManifold k M) S (interiorFamilyOn S f hi) := by
  intro a ha t ht x hx
  obtain ⟨c, rfl⟩ := ha
  have hxa : x.val ∈ c.ambient.source := by rwa [c.source_eq] at hx
  let y : IntrinsicInterior.Point k M := ⟨f t x.val, hi t ht x⟩
  obtain ⟨b, hba, hyb⟩ := IntrinsicInterior.exists_chart_from_atlas
    (chartAt (EuclideanHalfSpace (k + 1)) (f t x.val)) (chart_mem_atlas _ _) y
    (mem_chart_source _ _)
  obtain ⟨U, β, hU, hpU, hβ, heq⟩ :=
    hf.exists_coordinate_lift hS hfc c.ambient c.mem_atlas t ht x.val hxa
  have hcoord (z : IntrinsicInterior.Point k M) (hz : z ∈ c.chart.source) :
      c.chart z = c.ambient.extend (𝓡∂ (k + 1)) z.val := c.toFun_eq z hz
  have hβcenter : β (t.val, c.chart x) = b.chart y := by
    rw [hcoord x hx, b.toFun_eq y hyb, hba]
    exact (heq t ht x.val hxa hpU).2
  let O : TopologicalSpace.Opens (ℝ × Model (k + 1)) :=
    ⟨U ∩ β ⁻¹' b.chart.target,
      hβ.continuousOn.isOpen_inter_preimage hU b.chart.open_target⟩
  let g : O → IntrinsicInterior.Point k M := fun z => b.chart.symm (β z.val)
  have hbs : ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      b.chart.symm b.chart.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (show b.chart ∈ _root_.atlas (Model (k + 1))
        (IntrinsicInterior.Point k M) from ⟨b, rfl⟩))
  have hg : ContMDiff 𝓘(ℝ, ℝ × Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g := by
    intro z
    exact (hbs.contMDiffAt (b.chart.open_target.mem_nhds z.property.2)).comp z
      (((hβ.contDiffAt (hU.mem_nhds z.property.1)).contMDiffAt).comp
        z contMDiff_subtype_val.contMDiffAt)
  refine ⟨O, ?_, g, hg, ?_⟩
  · change (t.val, c.chart x) ∈ O
    refine ⟨by rw [hcoord x hx]; exact hpU, ?_⟩
    change β (t.val, c.chart x) ∈ b.chart.target
    rw [hβcenter]
    exact b.chart.map_source hyb
  · intro s hs z hz hsz
    let w := interiorFamilyOn S f hi s z
    have hwval : w.val = f s z.val := interiorFamilyOn_val hi hs z
    have hza : z.val ∈ c.ambient.source := by rwa [c.source_eq] at hz
    have hszU : (s.val, c.ambient.extend (𝓡∂ (k + 1)) z.val) ∈ U := by
      have h := hsz.1
      change (s.val, c.chart z) ∈ U at h
      rwa [hcoord z hz] at h
    have hwsource : w ∈ b.chart.source := by
      rw [b.source_eq, mem_preimage, hwval, hba]
      exact (heq s hs z.val hza hszU).1
    have hβz : β (s.val, c.chart z) = b.chart w := by
      rw [hcoord z hz, b.toFun_eq w hwsource, hwval, hba]
      exact (heq s hs z.val hza hszU).2
    change b.chart.symm (β (s.val, c.chart z)) = w
    rw [hβz, b.chart.left_inv hwsource]

variable {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]

omit [T2Space M] [SecondCountableTopology M] [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Interior preservation is derived from the actual compatible native
transition diffeomorphism. -/
theorem compatibleTransition_interior (e e' : Trivialization M (π M E))
    (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (he' : CompatibleTrivialization (𝓡∂ (k + 1)) E e')
    (t : Parameter) (ht : t ∈ e.baseSet ∩ e'.baseSet)
    (x : IntrinsicInterior.Point k M) :
    (𝓡∂ (k + 1)).IsInteriorPoint (e.coordChange e' t x.val) := by
  have hpre := Diffeomorph.preimage_interior (by simp)
    (compatibleTransitionDiffeomorph e e' he he' ht)
  have hx : x.val ∈ (compatibleTransitionDiffeomorph e e' he he' ht) ⁻¹'
      (𝓡∂ (k + 1)).interior M := by rw [hpre]; exact x.property
  exact hx

/-- Both ordered compatible transitions have actual real target-valued
interior germs, including near zero and one in the original parameter. -/
theorem compatibleTransition_interior_germs (e e' : Trivialization M (π M E))
    (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (he' : CompatibleTrivialization (𝓡∂ (k + 1)) E e') :
    HasSmoothManifoldTargetFamilyOn (IntrinsicInterior.smoothManifold k M)
      (IntrinsicInterior.smoothManifold k M) (e.baseSet ∩ e'.baseSet)
      (interiorFamilyOn (e.baseSet ∩ e'.baseSet) (e.coordChange e')
        (compatibleTransition_interior e e' he he')) := by
  exact ((he.hasSmoothTransition he').hasSmoothFamilyOn.interiorRestriction
    (e.open_baseSet.inter e'.open_baseSet) (continuousOn_coordChange e e')
    (compatibleTransition_interior e e' he he')).native_manifold
      (IntrinsicInterior.smoothManifold k M) (IntrinsicInterior.smoothManifold k M)

end FsFltz.Geometry.IntrinsicSmoothBundle
