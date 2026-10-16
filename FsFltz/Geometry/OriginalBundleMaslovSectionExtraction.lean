import FsFltz.Geometry.IntrinsicNativeCompletionEndSectionExtraction

/-!
# Native original section smoothness and coefficient extraction

Source: `geoemtric-part-fsf.tex`, smooth-extension convention, lines 119–122;
`def:maslov`, lines 212–232; and `sec:lean`, lines 788–814.
The section is arbitrary in the original canonical tensor-square fibers.
Its restriction has native bundle `ContMDiff` in the independently constructed
original interval-interior or full signed-cylinder prebundle. Scalar regularity
and full tensor reconstruction are derived, rather than supplied as germs.

Boundary-manifold `ContMDiff` alone is not the source's real-open extension
convention. Endpoint extensions and restriction from the whole original
completed total canonical bundle remain separate foundations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry

section InteriorParameter

variable {d : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (Model d) X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth scalar on the actual interval base has real-open local
extensions at strict interior times. Only a genuine spatial inverse chart
is used; no endpoint extension assertion is made. -/
theorem exists_realOpenScalarExtension_of_interiorParameter
    {V : Set F} (hV : IsOpen V) (ψ : F → X)
    (hψ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, Model d) ∞ ψ V)
    {U : Set (Parameter × X)} (hU : IsOpen U)
    (q : Parameter × X → ℂ)
    (hq : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, ℂ) ∞ q U)
    (t : Parameter) (ht : t.val ∈ Ioo (0 : ℝ) 1) (y : F)
    (hy : y ∈ V) (hUty : (t, ψ y) ∈ U) :
    ∃ W : TopologicalSpace.Opens (ℝ × F),
      (t.val, y) ∈ W ∧ (W : Set (ℝ × F)) ⊆ (Ioo (0 : ℝ) 1 ×ˢ V) ∧
      ∃ a : ℝ × F → ℂ, ContDiffOn ℝ ∞ a W ∧
        ∀ (s : Parameter) (z : F), (s.val, z) ∈ W → a (s.val, z) = q (s, ψ z) := by
  let r : ℝ × F → Parameter × X := fun z => (projIcc 0 1 (by norm_num) z.1, ψ z.2)
  have htime : ContMDiffOn 𝓘(ℝ, ℝ × F) (𝓡∂ 1) ∞
      (fun z : ℝ × F => projIcc 0 1 (by norm_num) z.1) (Ioo (0 : ℝ) 1 ×ˢ V) :=
    (contMDiffOn_projIcc (x := (0 : ℝ)) (y := 1)).comp contDiff_fst.contMDiff.contMDiffOn
      (fun _ hz => Ioo_subset_Icc_self hz.1)
  have hspace : ContMDiffOn 𝓘(ℝ, ℝ × F) 𝓘(ℝ, Model d) ∞
      (fun z : ℝ × F => ψ z.2) (Ioo (0 : ℝ) 1 ×ˢ V) :=
    hψ.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hz => hz.2)
  have hr : ContMDiffOn 𝓘(ℝ, ℝ × F)
      ((𝓡∂ 1).prod 𝓘(ℝ, Model d)) ∞ r (Ioo (0 : ℝ) 1 ×ˢ V) := by
    exact htime.prodMk hspace
  let W : TopologicalSpace.Opens (ℝ × F) :=
    ⟨(Ioo (0 : ℝ) 1 ×ˢ V) ∩ r ⁻¹' U,
      hr.continuousOn.isOpen_inter_preimage (isOpen_Ioo.prod hV) hU⟩
  have hrt : r (t.val, y) = (t, ψ y) := by
    simp only [r, projIcc_of_mem (by norm_num) t.property]
  refine ⟨W, ⟨⟨ht, hy⟩, by change r (t.val, y) ∈ U; rw [hrt]; exact hUty⟩,
    inter_subset_left, q ∘ r, ?_, ?_⟩
  · exact (hq.comp (hr.mono inter_subset_left) (fun _ hz => hz.2)).contDiffOn
  · intro s z _
    simp only [Function.comp_apply, r, projIcc_of_mem (by norm_num) s.property]

end InteriorParameter
end FsFltz.Geometry

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t b, C t (0, b) = b.val)
  (J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (N : Model (2 * n) ≃L[ℝ] Model (k + 1))
  (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)

local instance : ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ
local instance : ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
local instance : IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

/-- Intrinsic smoothness in the original interval-interior canonical-square
bundle. No coefficient extension or represented pair family occurs here. -/
def IsSmoothOriginalInteriorSection
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N) : Prop :=
  let a := originalInteriorCanonicalTensorSquareVectorPrebundle
    hδ C hemb hboundary hzero J N hC hinv hJ hJsq
  letI := a.totalSpaceTopology
  letI := a.toFiberBundle
  ContMDiff (familyModel (k + 1)) ((familyModel (k + 1)).prod 𝓘(ℝ, ℂ)) ∞
    (fun p => (⟨p, originalInteriorSection C J N σ p⟩ : Bundle.TotalSpace ℂ
      (fun p : Parameter × IntrinsicInterior.Point k M =>
        CanonicalTensorSquare (originalInteriorComplex C J N p))))

/-- Intrinsic smoothness in the original full signed-cylinder bundle,
including the seam. It uses the same original section as the interior. -/
def IsSmoothOriginalEndSection
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N) : Prop :=
  let a := originalEndCanonicalTensorSquareVectorPrebundle
    hδ C hemb hboundary hzero J N P hC hinv hJ hJsq
  letI := a.totalSpaceTopology
  letI := a.toFiberBundle
  ContMDiff (familyModel (k + 1)) ((familyModel (k + 1)).prod 𝓘(ℝ, ℂ)) ∞
    (fun p => (⟨p, originalEndSection C J N σ p⟩ : Bundle.TotalSpace ℂ
      (fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) =>
        CanonicalTensorSquare (originalEndComplex C J N p))))

namespace OriginalInteriorCanonicalChart

variable {hδ C hemb hboundary hzero J N hC hinv}
  (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))

/-- Every independently constructed original chart extracts a smooth
scalar from native section smoothness, including at both time endpoints. -/
theorem smooth_sectionCoefficient
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalInteriorSection hδ C hemb hboundary hzero J N hC hinv hJ hJsq σ) :
    ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℂ) ∞
      (fun p => c.tensorCoordinateLinearMap (P := N) p (originalInteriorSection C J N σ p))
      c.baseDomain := by
  let a := originalInteriorCanonicalTensorSquareVectorPrebundle
    hδ C hemb hboundary hzero J N hC hinv hJ hJsq
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  let := a.toVectorBundle
  let := a.contMDiffVectorBundle (n := ∞) (familyModel (k + 1))
  let e := a.trivializationOfMemPretrivializationAtlas
    (show c.tensorPretrivialization (P := N) hC hinv ∈ a.pretrivializationAtlas from ⟨c, rfl⟩)
  let : MemTrivializationAtlas e := ⟨_, ⟨c, rfl⟩, rfl⟩
  intro p hp
  have hs := (e.contMDiffAt_section_iff hp).mp (hσ p)
  exact hs.contMDiffWithinAt

include hC hinv in
/-- Nonvanishing is reflected by the actual original fiber coordinate. -/
theorem sectionCoefficient_ne_zero
    (σ : OriginalNativeCanonicalSection C J N)
    {p : Parameter × IntrinsicInterior.Point k M} (hp : p ∈ c.baseDomain)
    (hnσ : originalInteriorSection C J N σ p ≠ 0) :
    c.tensorCoordinateLinearMap (P := N) p (originalInteriorSection C J N σ p) ≠ 0 := by
  intro hzero
  apply hnσ
  apply (c.tensorCoordinateEquiv (P := N) hC hinv p hp).injective
  change c.tensorCoordinateLinearMap (P := N) p (originalInteriorSection C J N σ p) =
    c.tensorCoordinateLinearMap (P := N) p 0
  simpa only [map_zero] using hzero

/-- Native bundle smoothness supplies the existing real-open coefficient
germ at every strict interior time, in any original spatial chart. -/
theorem sectionCoefficientExtension_of_interiorParameter
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalInteriorSection hδ C hemb hboundary hzero J N hC hinv hJ hJsq σ)
    (p : Parameter × IntrinsicInterior.Point k M) (hp : p ∈ c.baseDomain)
    (ht : p.1.val ∈ Ioo (0 : ℝ) 1) : c.HasSectionCoefficientExtension (P := N) σ p := by
  let e := chartAt (Model (k + 1)) c.anchor
  obtain ⟨W, hpW, hW, a, ha, heq⟩ := exists_realOpenScalarExtension_of_interiorParameter
    e.open_target e.symm (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (k + 1))) (x := c.anchor))
    c.isOpen_baseDomain
    (fun z => c.tensorCoordinateLinearMap (P := N) z (originalInteriorSection C J N σ z))
    (c.smooth_sectionCoefficient hJ hJsq σ hσ) p.1 ht (e p.2) (e.map_source hp.1.2)
    (by rw [e.left_inv hp.1.2]; exact hp)
  let V : TopologicalSpace.Opens (ℝ × Model (k + 1)) := ⟨W ∩ c.domain, W.isOpen.inter c.domain.isOpen⟩
  refine ⟨V, a, ⟨hpW, hp.2⟩, inter_subset_right, ha.mono inter_subset_left, ?_⟩
  intro s w hw hsw
  rw [heq s (e w) hsw.1, e.left_inv hw]

end OriginalInteriorCanonicalChart

namespace OriginalEndCanonicalChart

variable {hδ C hemb hboundary hzero J N P hC hinv}
  (c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))

/-- The full signed cylinder extracts coefficients in every original chart
from native bundle smoothness, with no scalar regularity hypothesis. -/
theorem smooth_sectionCoefficient
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalEndSection hδ C hemb hboundary hzero J N P hC hinv hJ hJsq σ) :
    ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℂ) ∞
      (fun p => c.tensorCoordinateLinearMap (N := N) p (originalEndSection C J N σ p))
      c.baseDomain := by
  let a := originalEndCanonicalTensorSquareVectorPrebundle
    hδ C hemb hboundary hzero J N P hC hinv hJ hJsq
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  let := a.toVectorBundle
  let := a.contMDiffVectorBundle (n := ∞) (familyModel (k + 1))
  let e := a.trivializationOfMemPretrivializationAtlas
    (show c.tensorPretrivialization (N := N) hC hinv ∈ a.pretrivializationAtlas from ⟨c, rfl⟩)
  let : MemTrivializationAtlas e := ⟨_, ⟨c, rfl⟩, rfl⟩
  intro p hp
  have hs := (e.contMDiffAt_section_iff hp).mp (hσ p)
  exact hs.contMDiffWithinAt

include hC hinv in
/-- The native section is nonzero exactly when its cylinder coefficient is. -/
theorem sectionCoefficient_ne_zero
    (σ : OriginalNativeCanonicalSection C J N)
    {p : Parameter × Band δ (IntrinsicBoundary.Point k M)} (hp : p ∈ c.baseDomain)
    (hnσ : originalEndSection C J N σ p ≠ 0) :
    c.tensorCoordinateLinearMap (N := N) p (originalEndSection C J N σ p) ≠ 0 := by
  intro hzero
  apply hnσ
  apply (c.tensorCoordinateEquiv (N := N) hC hinv p hp).injective
  change c.tensorCoordinateLinearMap (N := N) p (originalEndSection C J N σ p) =
    c.tensorCoordinateLinearMap (N := N) p 0
  simpa only [map_zero] using hzero

/-- Full signed-cylinder coefficients also have real-open germs at strict
interior times. The spatial inverse uses the actual radial sign and band. -/
theorem sectionCoefficientExtension_of_interiorParameter
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalEndSection hδ C hemb hboundary hzero J N P hC hinv hJ hJsq σ)
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) (hp : p ∈ c.baseDomain)
    (ht : p.1.val ∈ Ioo (0 : ℝ) 1) : c.HasSectionCoefficientExtension (N := N) σ p := by
  classical
  let e := chartAt (Model k × ℝ) c.anchor
  let B : Set (IntrinsicBoundary.Point k M × ℝ) := {v | -v.2 < δ}
  have hB : IsOpen B := isOpen_lt continuous_snd.neg continuous_const
  let q : IntrinsicBoundary.Point k M × ℝ → Band δ (IntrinsicBoundary.Point k M) :=
    fun v => if h : -v.2 < δ then ⟨(-v.2, v.1), h, mem_univ _⟩ else p.2
  have hq : ContMDiffOn 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model (k + 1)) ∞ q B := by
    intro v hv
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_band_iff_val.mpr
    have hraw : ContMDiff 𝓘(ℝ, Model k × ℝ)
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞
        (fun v : IntrinsicBoundary.Point k M × ℝ => (-v.2, v.1)) := by
      rw [modelWithCornersSelf_prod (E := Model k) (F := ℝ)]
      exact contMDiff_snd.neg.prodMk contMDiff_fst
    apply hraw.contMDiffAt.congr_of_eventuallyEq
    filter_upwards [hB.mem_nhds hv] with v hv
    change -v.2 < δ at hv
    simp only [q, Function.comp_apply, dite_eq_left hv]
  have hqleft : ∀ w : Band δ (IntrinsicBoundary.Point k M), q (endBandCoordinates w) = w := by
    intro w
    have hw : -(endBandCoordinates w).2 < δ := by
      simpa only [endBandCoordinates, neg_neg] using (show w.val.1 < δ from w.property.1)
    apply Subtype.ext
    dsimp only [q]
    rw [dite_eq_left hw]
    simp only [endBandCoordinates, neg_neg]
  let D : Set (Model k × ℝ) := e.target ∩ e.symm ⁻¹' B
  have he : ContMDiffOn 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ) ∞ e.symm e.target :=
    contMDiffOn_chart_symm (I := 𝓘(ℝ, Model k × ℝ)) (x := c.anchor)
  have hD : IsOpen D := he.continuousOn.isOpen_inter_preimage e.open_target hB
  have hψ : ContMDiffOn 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model (k + 1)) ∞ (q ∘ e.symm) D :=
    hq.comp (he.mono inter_subset_left) (fun _ hz => hz.2)
  have hcenter : e (endBandCoordinates p.2) ∈ D := by
    refine ⟨e.map_source hp.1.2, ?_⟩
    change e.symm (e (endBandCoordinates p.2)) ∈ B
    rw [e.left_inv hp.1.2]
    change -(-p.2.val.1) < δ
    simpa only [neg_neg] using (show p.2.val.1 < δ from p.2.property.1)
  obtain ⟨W, hpW, _, a, ha, heq⟩ := exists_realOpenScalarExtension_of_interiorParameter
    hD (q ∘ e.symm) hψ c.isOpen_baseDomain
    (fun z => c.tensorCoordinateLinearMap (N := N) z (originalEndSection C J N σ z))
    (c.smooth_sectionCoefficient hJ hJsq σ hσ) p.1 ht (e (endBandCoordinates p.2)) hcenter
    (by simp only [Function.comp_apply, e.left_inv hp.1.2, hqleft]; exact hp)
  let V : TopologicalSpace.Opens (ℝ × (Model k × ℝ)) :=
    ⟨W ∩ c.domain, W.isOpen.inter c.domain.isOpen⟩
  refine ⟨V, a, ⟨hpW, hp.2⟩, inter_subset_right, ha.mono inter_subset_left, ?_⟩
  intro s w hw hsw
  rw [heq s (e (endBandCoordinates w)) hsw.1]
  change c.tensorCoordinateLinearMap (N := N) (s, q (e.symm (e (endBandCoordinates w))))
    (originalEndSection C J N σ (s, q (e.symm (e (endBandCoordinates w))))) = _
  rw [e.left_inv hw, hqleft]

end OriginalEndCanonicalChart

/-- The remaining interior coefficient-extension input is needed only at
the two parameter endpoints. Every other parameter is produced from native
bundle smoothness, in each original canonical chart. -/
theorem originalInteriorSectionExtensions_of_nativeSmooth_and_endpoints
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalInteriorSection hδ C hemb hboundary hzero J N hC hinv hJ hJsq σ)
    (hend : ∀ (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
      (p : Parameter × IntrinsicInterior.Point k M), p ∈ c.baseDomain →
      p.1.val = 0 ∨ p.1.val = 1 → c.HasSectionCoefficientExtension (P := N) σ p) :
    HasOriginalInteriorSectionExtensions hδ C hemb hboundary hzero J N σ := by
  intro c p hp
  by_cases hzero : p.1.val = 0
  · exact hend c p hp (Or.inl hzero)
  by_cases hone : p.1.val = 1
  · exact hend c p hp (Or.inr hone)
  exact c.sectionCoefficientExtension_of_interiorParameter hJ hJsq σ hσ p hp
    ⟨lt_of_le_of_ne p.1.property.1 (Ne.symm hzero), lt_of_le_of_ne p.1.property.2 hone⟩

/-- The signed cylinder has precisely the same endpoint-only residual;
no coefficient germs at an interior parameter are input. -/
theorem originalEndSectionExtensions_of_nativeSmooth_and_endpoints
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalEndSection hδ C hemb hboundary hzero J N P hC hinv hJ hJsq σ)
    (hend : ∀ (c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
      (p : Parameter × Band δ (IntrinsicBoundary.Point k M)), p ∈ c.baseDomain →
      p.1.val = 0 ∨ p.1.val = 1 → c.HasSectionCoefficientExtension (N := N) σ p) :
    HasOriginalEndSectionExtensions hδ C hemb hboundary hzero J N σ := by
  intro c p hp
  by_cases hzero : p.1.val = 0
  · exact hend c p hp (Or.inl hzero)
  by_cases hone : p.1.val = 1
  · exact hend c p hp (Or.inr hone)
  exact c.sectionCoefficientExtension_of_interiorParameter hJ hJsq σ hσ p hp
    ⟨lt_of_le_of_ne p.1.property.1 (Ne.symm hzero), lt_of_le_of_ne p.1.property.2 hone⟩

/-- The actual native-section/coframe consumer now asks for coefficient
extensions only at zero and one. Native smoothness supplies every other
original interior parameter, preserving the full original tensor slots. -/
theorem originalNativeInteriorGradingSectionGerms_of_nativeSmooth_and_endpoints
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalInteriorSection hδ C hemb hboundary hzero J N hC hinv hJ hJsq σ)
    (hend : ∀ (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
      (p : Parameter × IntrinsicInterior.Point k M), p ∈ c.baseDomain →
      p.1.val = 0 ∨ p.1.val = 1 → c.HasSectionCoefficientExtension (P := N) σ p)
    (hnσ : ∀ s x, σ s x ≠ 0) :
    PairDeformation.HasNativeInteriorGradingSectionGerms hδ C hemb hboundary hzero
      J (originalNativeSectionTensor C J N σ) N := by
  have hs := originalInteriorSectionExtensions_of_nativeSmooth_and_endpoints
    hδ C hemb hboundary hzero J N hC hinv hJ hJsq σ hσ hend
  apply originalNativeInteriorGradingSectionGerms hδ C hemb hboundary hzero J N hC hinv
    hJ hJsq σ _ hnσ
  intro p
  let c := originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J N hC hinv hJ hJsq p
  have hp : p ∈ c.baseDomain :=
    mem_originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J N hC hinv hJ hJsq p
  exact ⟨c, hp, hs c p hp⟩

/-- The full signed-cylinder grading consumer retains the same original
section and tensor, with only the endpoint extension obligations supplied. -/
theorem originalNativeEndGradingSectionGerms_of_nativeSmooth_and_endpoints
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : IsSmoothOriginalEndSection hδ C hemb hboundary hzero J N P hC hinv hJ hJsq σ)
    (hend : ∀ (c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
      (p : Parameter × Band δ (IntrinsicBoundary.Point k M)), p ∈ c.baseDomain →
      p.1.val = 0 ∨ p.1.val = 1 → c.HasSectionCoefficientExtension (N := N) σ p)
    (hnσ : ∀ s x, σ s x ≠ 0) :
    PairDeformation.HasNativeEndGradingSectionGerms hδ C hemb hboundary hzero
      J (originalNativeSectionTensor C J N σ) P := by
  have hs := originalEndSectionExtensions_of_nativeSmooth_and_endpoints
    hδ C hemb hboundary hzero J N P hC hinv hJ hJsq σ hσ hend
  apply originalNativeEndGradingSectionGerms hδ C hemb hboundary hzero J N P hC hinv
    hJ hJsq σ _ hnσ
  intro p
  let c := originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq p
  have hp : p ∈ c.baseDomain :=
    mem_originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq p
  exact ⟨c, hp, hs c p hp⟩

end FsFltz.Geometry.IntrinsicCompletionGluing
