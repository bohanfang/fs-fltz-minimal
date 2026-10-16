import FsFltz.Geometry.IntrinsicNativeCompletionCanonicalExtensionAtlas

/-!
# Neighborhoods in the original canonical coordinates

Source: `geoemtric-part-fsf.tex`, smooth-extension convention (119–122),
`def:maslov` (212–244), and `sec:lean` (766–836). These are topological
neighborhood transfers for the actual branch inclusions. The real parameter
projection is used only in a continuous inverse; it asserts no smooth
extension across the endpoints of the original parameter interval.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

/-- Boundary and outward radius, with the sign dictated by inward collar time. -/
def coordinateRadiusHomeomorph {B : Type*} [TopologicalSpace B] :
    (ℝ × B) ≃ₜ (B × ℝ) where
  toFun z := (z.2, -z.1)
  invFun z := (-z.2, z.1)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_snd.prodMk continuous_fst.neg
  continuous_invFun := continuous_snd.neg.prodMk continuous_fst

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] {δ : ℝ}

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The literal cylindrical-band coordinates are an open embedding for the
inherited native topology. -/
theorem isOpenEmbedding_endBandCoordinates :
    IsOpenEmbedding (endBandCoordinates (k := k) (M := M) (δ := δ)) := by
  exact coordinateRadiusHomeomorph.isOpenEmbedding.comp
    (isOpen_Iio.prod isOpen_univ).isOpenEmbedding_subtypeVal

section ParameterSpatial

variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]

/-- A neighborhood in the actual interval and spatial manifold pulls back
to a real-open neighborhood of its literal coordinates. -/
theorem exists_parameterSpatialCoordinate_neighborhood
    (e : OpenPartialHomeomorph X E) (t : Parameter) (x : X) (hx : x ∈ e.source)
    {O : Set (Parameter × X)} (hO : IsOpen O) (hpO : (t, x) ∈ O) :
    ∃ V : TopologicalSpace.Opens (ℝ × E), (t.val, e x) ∈ V ∧
      ∀ (s : Parameter) (y : X), y ∈ e.source → (s.val, e y) ∈ V → (s, y) ∈ O := by
  let r : ℝ × E → Parameter × X := fun z =>
    (projIcc 0 1 (by norm_num) z.1, e.symm z.2)
  have hrp : r (t.val, e x) = (t, x) := by
    simp only [r, projIcc_of_mem (by norm_num) t.property, e.left_inv hx]
  have hrc : ContinuousAt r (t.val, e x) :=
    (continuous_projIcc.comp continuous_fst).continuousAt.prodMk
      ((e.continuousAt_symm (e.map_source hx)).comp_of_eq
        (continuous_snd.continuousAt (x := (t.val, e x))) rfl)
  have hn : r ⁻¹' O ∈ 𝓝 (t.val, e x) :=
    hrc.preimage_mem_nhds (hO.mem_nhds (hrp ▸ hpO))
  obtain ⟨V, hVO, hV, hpV⟩ := mem_nhds_iff.mp hn
  refine ⟨⟨V, hV⟩, hpV, ?_⟩
  intro s y hy hsy
  have h := hVO hsy
  simpa only [mem_preimage, r, projIcc_of_mem (by norm_num) s.property, e.left_inv hy]
    using h

end ParameterSpatial

variable (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t b, C t (0, b) = b.val)
  (J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))

local instance coordinateTopologyProductCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

namespace OriginalTotalCanonicalChart

variable {hδ C hemb hboundary hzero J}

instance nativeBaseTopology
    (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    TopologicalSpace c.NativeBase := match c with
  | .inl _ => inferInstanceAs (TopologicalSpace (Parameter × IntrinsicInterior.Point k M))
  | .inr _ => inferInstanceAs (TopologicalSpace (Parameter × Band δ (IntrinsicBoundary.Point k M)))

/-- Native-domain membership retains the original real chart domain. -/
theorem baseCoordinate_mem_realDomain
    (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    {p : c.NativeBase} (hp : p ∈ c.nativeDomain) : c.baseCoordinate p ∈ c.realDomain := by
  cases c <;> exact hp.2

/-- The raw coordinates are continuous on their actual native domain. -/
theorem continuousOn_baseCoordinate
    (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    ContinuousOn c.baseCoordinate c.nativeDomain := by
  cases c with
  | inl c =>
    let e := chartAt (Model (k + 1)) c.anchor
    exact ((continuous_subtype_val.comp continuous_fst).continuousOn.prodMk
      (e.continuousOn.comp continuous_snd.continuousOn (fun _ hp => hp.2))).mono
      inter_subset_left
  | inr c =>
    let e := chartAt (Model k × ℝ) c.anchor
    exact ((continuous_subtype_val.comp continuous_fst).continuousOn.prodMk
      (e.continuousOn.comp
        (isOpenEmbedding_endBandCoordinates.continuous.comp continuous_snd).continuousOn
        (fun _ hp => hp.2))).mono inter_subset_left

variable (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))

include hδ hzero hjoint in
/-- The branch inclusion is continuous in the actual quotient topology. -/
theorem continuous_inclusion
    (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    Continuous c.inclusion := by
  cases c with
  | inl c => exact (isOpenEmbedding_totalInterior hδ (fun t p => C t p.val) hzero hjoint).continuous
  | inr c => exact (isOpenEmbedding_totalCylinder (fun t p => C t p.val) hjoint).continuous

include hδ hzero hjoint in
/-- Every open neighborhood of an actual branch point contains the retained
native points of some real-open coordinate neighborhood of that same point. -/
theorem exists_rawCoordinate_neighborhood
    (c : OriginalTotalCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (p : c.NativeBase) (hp : p ∈ c.nativeDomain)
    {O : Set (TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val))}
    (hO : IsOpen O) (hpO : c.inclusion p ∈ O) :
    ∃ V : TopologicalSpace.Opens c.RealBase,
      c.baseCoordinate p ∈ V ∧ (V : Set c.RealBase) ⊆ c.realDomain ∧
      ∀ q : c.NativeBase, q ∈ c.nativeDomain →
        c.baseCoordinate q ∈ V → c.inclusion q ∈ O := by
  have hpre : IsOpen (c.inclusion ⁻¹' O) := hO.preimage (c.continuous_inclusion hjoint)
  have hret : ∃ V : TopologicalSpace.Opens c.RealBase,
      c.baseCoordinate p ∈ V ∧
      ∀ q : c.NativeBase, q ∈ c.nativeDomain →
        c.baseCoordinate q ∈ V → c.inclusion q ∈ O := by
    cases c with
    | inl c =>
      obtain ⟨V, hpV, hV⟩ := exists_parameterSpatialCoordinate_neighborhood
        (chartAt (Model (k + 1)) c.anchor) p.1 p.2 hp.1.2 hpre hpO
      exact ⟨V, hpV, fun q hq hqV => hV q.1 q.2 hq.1.2 hqV⟩
    | inr c =>
      let : Nonempty (Band δ (IntrinsicBoundary.Point k M)) := ⟨p.2⟩
      let e : OpenPartialHomeomorph (Band δ (IntrinsicBoundary.Point k M)) (Model k × ℝ) :=
        (isOpenEmbedding_endBandCoordinates.toOpenPartialHomeomorph
          endBandCoordinates).trans (chartAt (Model k × ℝ) c.anchor)
      have hpE : p.2 ∈ e.source := ⟨mem_univ _, hp.1.2⟩
      obtain ⟨V, hpV, hV⟩ := exists_parameterSpatialCoordinate_neighborhood
        e p.1 p.2 hpE hpre hpO
      exact ⟨V, hpV, fun q hq hqV => hV q.1 q.2 ⟨mem_univ _, hq.1.2⟩ hqV⟩
  obtain ⟨V, hpV, hV⟩ := hret
  refine ⟨V ⊓ c.realDomain, ⟨hpV, c.baseCoordinate_mem_realDomain hp⟩,
    inter_subset_right, ?_⟩
  intro q hq hqV
  exact hV q hq hqV.1

end OriginalTotalCanonicalChart
end FsFltz.Geometry.IntrinsicCompletionGluing
