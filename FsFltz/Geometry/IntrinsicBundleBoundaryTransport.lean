import FsFltz.Geometry.IntrinsicBundleDataTransport

/-!
# Actual boundary-valued joint transition germs

Source: `geoemtric-part-fsf.tex`, `def:chain`, 163–169, and `sec:lean`,
788–814. Joint ambient extension germs and native boundary preservation
produce joint extensions with values in the actual intrinsic boundary.
Boundary preservation is required only at the original interval parameters.
The extension is constructed by inserting, deleting and then inverting
actual boundary chart coordinates.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle

namespace FsFltz.Geometry.IntrinsicBoundary

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

omit [T2Space M] [SecondCountableTopology M] in
/-- Restrict a specified native chart, retaining its identity. This allows
the boundary transport proof to use precisely the ambient target chart
named by its joint extension germ. -/
theorem exists_chart_from_atlas
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)))
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    (x : Point k M) (hx : x.val ∈ e.source) :
    ∃ c : Chart k M, c.ambient = e ∧ x ∈ c.chart.source := by
  have himage : e.IsImage ((𝓡∂ (k + 1)).boundary M)
      {v : EuclideanHalfSpace (k + 1) | v.val 0 = 0} := by
    intro y hy
    exact (isBoundaryPoint_iff_chart_zero he hy).symm
  obtain ⟨r, hrs, hrt, hrf, hrg⟩ := exists_openPartialHomeomorph_subtypes e himage x
    ⟨halfSpaceInsert k 0, by simp⟩
  let q := r.trans (halfSpaceBoundaryHomeomorph k).toOpenPartialHomeomorph
  refine ⟨⟨e, he, q, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · change r.source ∩ r ⁻¹' univ = _
    rw [preimage_univ, inter_univ]
    exact hrs
  · change univ ∩ (halfSpaceBoundaryHomeomorph k).symm ⁻¹' r.target = _
    rw [univ_inter, hrt]
    rfl
  · intro y hy
    change boundaryDrop k (r y).val.val = boundaryDrop k (e y.val).val
    rw [hrf y hy.1]
  · intro v hv
    change (r.symm ((halfSpaceBoundaryHomeomorph k).symm v)).val = _
    exact hrg _ hv.2
  · change x ∈ r.source ∩ r ⁻¹' univ
    rw [hrs]
    exact ⟨hx, mem_univ _⟩

omit [T2Space M] [SecondCountableTopology M] in
/-- Boundary coordinates insert into the full ambient coordinates literally. -/
theorem Chart.extend_eq_insert (c : Chart k M) (x : Point k M)
    (hx : x ∈ c.chart.source) :
    c.ambient.extend (𝓡∂ (k + 1)) x.val = boundaryInsert k (c.chart x) := by
  have hxa : x.val ∈ c.ambient.source := by rwa [c.source_eq] at hx
  rw [c.toFun_eq x hx]
  have hz := (isBoundaryPoint_iff_chart_zero c.mem_atlas hxa).mp x.property
  exact (boundaryInsert_drop (c.ambient x.val).val hz).symm

end FsFltz.Geometry.IntrinsicBoundary

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The actual induced native boundary map on the parameter set. Values
outside that set are irrelevant and are assigned the identity. -/
def boundaryFamilyOn (S : Set Parameter) (f : Parameter → M → M)
    (hb : ∀ t ∈ S, ∀ x : IntrinsicBoundary.Point k M,
      (𝓡∂ (k + 1)).IsBoundaryPoint (f t x.val)) :
    Parameter → IntrinsicBoundary.Point k M → IntrinsicBoundary.Point k M :=
  by
    classical
    exact fun t x => if h : t ∈ S then ⟨f t x.val, hb t h x⟩ else x

omit [T2Space M] [SecondCountableTopology M] [IsManifold (𝓡∂ (k + 1)) ∞ M] in
@[simp]
theorem boundaryFamilyOn_val {S : Set Parameter} {f : Parameter → M → M}
    (hb : ∀ t ∈ S, ∀ x : IntrinsicBoundary.Point k M,
      (𝓡∂ (k + 1)).IsBoundaryPoint (f t x.val)) {t : Parameter} (ht : t ∈ S)
    (x : IntrinsicBoundary.Point k M) :
    (boundaryFamilyOn S f hb t x).val = f t x.val := by
  simp only [boundaryFamilyOn, dite_eq_left ht]

/-- Restriction of joint ambient germs gives actual boundary-valued germs.
The produced off-interval map need not preserve the ambient boundary: its
values are constructed in a fixed native boundary chart instead. -/
theorem HasSmoothFamilyOn.boundaryRestriction {S : Set Parameter} (hS : IsOpen S)
    {f : Parameter → M → M} (hf : HasSmoothFamilyOn (𝓡∂ (k + 1)) S f)
    (hfc : ContinuousOn (fun p : Parameter × M => f p.1 p.2) (S ×ˢ univ))
    (hb : ∀ t ∈ S, ∀ x : IntrinsicBoundary.Point k M,
      (𝓡∂ (k + 1)).IsBoundaryPoint (f t x.val)) :
    HasSmoothTargetFamilyOn 𝓘(ℝ, Model k) (IntrinsicBoundary.smoothManifold k M) S
      (boundaryFamilyOn S f hb) := by
  intro a ha t ht x hx
  obtain ⟨c, rfl⟩ := ha
  have hxa : x.val ∈ c.ambient.source := by rwa [c.source_eq] at hx
  let y : IntrinsicBoundary.Point k M := ⟨f t x.val, hb t ht x⟩
  obtain ⟨b, hba, hyb⟩ := IntrinsicBoundary.exists_chart_from_atlas
    (chartAt (EuclideanHalfSpace (k + 1)) (f t x.val)) (chart_mem_atlas _ _) y
    (mem_chart_source _ _)
  obtain ⟨U, β, hU, hpU, hβ, heq⟩ :=
    hf.exists_coordinate_lift hS hfc c.ambient c.mem_atlas t ht x.val hxa
  let p : ℝ × Model k → ℝ × Model (k + 1) :=
    fun z => (z.1, boundaryInsert k z.2)
  have hp : ContDiff ℝ ∞ p :=
    contDiff_fst.prodMk ((boundaryInsert k).contDiff.comp contDiff_snd)
  let q : ℝ × Model k → Model k := fun z => boundaryDrop k (β (p z))
  have hq : ContDiffOn ℝ ∞ q (p ⁻¹' U) :=
    (boundaryDrop k).contDiff.comp_contDiffOn
      (hβ.comp hp.contDiffOn (fun _ hz => hz))
  have hpcenter : p (t.val, c.chart x) = (t.val, c.ambient.extend (𝓡∂ (k + 1)) x.val) :=
    Prod.ext rfl (c.extend_eq_insert x hx).symm
  have hβcenter : β (p (t.val, c.chart x)) = b.ambient.extend (𝓡∂ (k + 1)) y.val := by
    rw [hpcenter, hba]
    exact (heq t ht x.val hxa hpU).2
  have hqcenter : q (t.val, c.chart x) = b.chart y := by
    change boundaryDrop k (β (p (t.val, c.chart x))) = _
    rw [hβcenter, b.extend_eq_insert y hyb, boundaryDrop_insert]
  let O : TopologicalSpace.Opens (ℝ × Model k) :=
    ⟨p ⁻¹' U ∩ q ⁻¹' b.chart.target,
      hq.continuousOn.isOpen_inter_preimage (hU.preimage hp.continuous) b.chart.open_target⟩
  let g : O → IntrinsicBoundary.Point k M := fun z => b.chart.symm (q z.val)
  have hbs : ContMDiffOn 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) ∞ b.chart.symm b.chart.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (show b.chart ∈ atlas (Model k)
        (IntrinsicBoundary.Point k M) from ⟨b, rfl⟩))
  have hg : ContMDiff 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model k) ∞ g := by
    intro z
    exact (hbs.contMDiffAt (b.chart.open_target.mem_nhds z.property.2)).comp z
      (((hq.contDiffAt ((hU.preimage hp.continuous).mem_nhds z.property.1)).contMDiffAt).comp
        z contMDiff_subtype_val.contMDiffAt)
  refine ⟨O, ?_, g, hg, ?_⟩
  · change (t.val, c.chart x) ∈ O
    refine ⟨by change p (t.val, c.chart x) ∈ U; rw [hpcenter]; exact hpU, ?_⟩
    change q (t.val, c.chart x) ∈ b.chart.target
    rw [hqcenter]
    exact b.chart.map_source hyb
  · intro s hs z hz hsz
    let w := boundaryFamilyOn S f hb s z
    have hwval : w.val = f s z.val := boundaryFamilyOn_val hb hs z
    have hza : z.val ∈ c.ambient.source := by rwa [c.source_eq] at hz
    have hpz : p (s.val, c.chart z) =
        (s.val, c.ambient.extend (𝓡∂ (k + 1)) z.val) :=
      Prod.ext rfl (c.extend_eq_insert z hz).symm
    have hβz : β (p (s.val, c.chart z)) = b.ambient.extend (𝓡∂ (k + 1)) w.val := by
      rw [hpz, hwval, hba]
      have hszU : (s.val, c.ambient.extend (𝓡∂ (k + 1)) z.val) ∈ U := by
        have h := hsz.1
        change p (s.val, c.chart z) ∈ U at h
        rwa [hpz] at h
      exact (heq s hs z.val hza hszU).2
    have hcoord : q (s.val, c.chart z) = boundaryDrop k
        (b.ambient w.val).val := by
      change boundaryDrop k (β (p (s.val, c.chart z))) = _
      rw [hβz]
      rfl
    have hwsource : w ∈ b.chart.source := by
      rw [b.source_eq]
      change w.val ∈ b.ambient.source
      rw [hwval, hba]
      have hszU : (s.val, c.ambient.extend (𝓡∂ (k + 1)) z.val) ∈ U := by
        have h := hsz.1
        change p (s.val, c.chart z) ∈ U at h
        rwa [hpz] at h
      exact (heq s hs z.val hza hszU).1
    change b.chart.symm (q (s.val, c.chart z)) = w
    rw [hcoord, ← b.toFun_eq w hwsource, b.chart.left_inv hwsource]

end FsFltz.Geometry.IntrinsicSmoothBundle

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (TotalSpace M E)] [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]

/-- Compatible charts, including the produced global chart, induce actual
native fibre diffeomorphisms in either direction. -/
def compatibleTransitionDiffeomorph (e e' : Trivialization M (π M E))
    (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (he' : CompatibleTrivialization (𝓡∂ (k + 1)) E e')
    {t : Parameter} (ht : t ∈ e.baseSet ∩ e'.baseSet) :
    Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞ where
  __ := (e.coordChangeHomeomorph e' ht.1 ht.2).toEquiv
  contMDiff_toFun := (he.hasSmoothTransition he').contMDiff ht
  contMDiff_invFun := (he'.hasSmoothTransition he).contMDiff ⟨ht.2, ht.1⟩

/-- The native boundary is preserved by every compatible transition. -/
theorem compatibleTransition_boundary (e e' : Trivialization M (π M E))
    (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (he' : CompatibleTrivialization (𝓡∂ (k + 1)) E e')
    (t : Parameter) (ht : t ∈ e.baseSet ∩ e'.baseSet)
    (x : IntrinsicBoundary.Point k M) :
    (𝓡∂ (k + 1)).IsBoundaryPoint (e.coordChange e' t x.val) := by
  have hpre := Diffeomorph.preimage_boundary (by simp)
    (compatibleTransitionDiffeomorph e e' he he' ht)
  have hx : x.val ∈ (compatibleTransitionDiffeomorph e e' he he' ht) ⁻¹'
      (𝓡∂ (k + 1)).boundary M := by
    rw [hpre]
    exact x.property
  exact hx

/-- Ambient compatible transitions supply actual boundary-valued joint
germs without adding a boundary-smoothness input. -/
theorem compatibleTransition_boundary_germs (e e' : Trivialization M (π M E))
    (he : CompatibleTrivialization (𝓡∂ (k + 1)) E e)
    (he' : CompatibleTrivialization (𝓡∂ (k + 1)) E e') :
    HasSmoothTargetFamilyOn 𝓘(ℝ, Model k) (IntrinsicBoundary.smoothManifold k M)
      (e.baseSet ∩ e'.baseSet)
      (boundaryFamilyOn (e.baseSet ∩ e'.baseSet) (e.coordChange e')
        (compatibleTransition_boundary e e' he he')) := by
  exact (he.hasSmoothTransition he').hasSmoothFamilyOn.boundaryRestriction
    (e.open_baseSet.inter e'.open_baseSet) (continuousOn_coordChange e e')
      (compatibleTransition_boundary e e' he he')

end FsFltz.Geometry.IntrinsicSmoothBundle
