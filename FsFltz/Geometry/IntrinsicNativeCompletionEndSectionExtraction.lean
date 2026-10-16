import FsFltz.Geometry.IntrinsicNativeCompletionEndCanonicalBundle
import FsFltz.Geometry.IntrinsicNativeCompletionInteriorSectionExtraction

/-!
# Original cylindrical-end sections give grading graph extensions

Source: `geoemtric-part-fsf.tex`, lines 119–122 (open smooth extension),
`def:maslov`, lines 212–232, and `sec:lean`, lines 788–814. One original
section is restricted to the full original cylinder band, including the seam
and negative outward radii. Local scalar germs in the independently constructed
original end bundle produce the native graph and full tensor identities.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

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

local instance : ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ
local instance : ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
local instance : IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ)) (IntrinsicBoundary.Point k M) ℝ

variable
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)

/-- Restriction of the same original section to the full cylinder band. -/
def originalEndSection (σ : OriginalNativeCanonicalSection C J N)
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) :
    CanonicalTensorSquare (originalEndComplex C J N p) :=
  σ p.1 (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C p.1 q.val) p.2)

variable {hδ C hemb hboundary hzero J}

/-- A scalar germ in one original bundle chart, with the source's explicit
open-extension convention at interval endpoints. -/
def OriginalEndCanonicalChart.HasSectionCoefficientExtension
    (c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (σ : OriginalNativeCanonicalSection C J N) (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) : Prop :=
  ∃ (U : TopologicalSpace.Opens (ℝ × (Model k × ℝ))) (q : (ℝ × (Model k × ℝ)) → ℂ),
    (p.1.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates p.2)) ∈ U ∧
    (U : Set (ℝ × (Model k × ℝ))) ⊆ c.domain ∧ ContDiffOn ℝ ∞ q U ∧
    ∀ (s : Parameter) (w : Band δ (IntrinsicBoundary.Point k M)),
      endBandCoordinates w ∈ (chartAt (Model k × ℝ) c.anchor).source →
      (s.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates w)) ∈ U →
      q (s.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates w)) =
        c.tensorCoordinateLinearMap (N := N) (s, w) (originalEndSection C J N σ (s, w))

variable (hδ C hemb hboundary hzero J)

/-- Source smoothness asks for a coefficient germ in some original bundle
chart near each point; no selected target chart or graph is supplied. -/
def HasOriginalEndLocalSectionExtensions (σ : OriginalNativeCanonicalSection C J N) : Prop :=
  ∀ p : Parameter × Band δ (IntrinsicBoundary.Point k M),
    ∃ c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n),
      p ∈ c.baseDomain ∧ c.HasSectionCoefficientExtension (N := N) σ p

/-- All-chart form, derived below from the local source convention. -/
def HasOriginalEndSectionExtensions (σ : OriginalNativeCanonicalSection C J N) : Prop :=
  ∀ (c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M)), p ∈ c.baseDomain →
    c.HasSectionCoefficientExtension (N := N) σ p

namespace OriginalEndCanonicalChart

variable (c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
variable {hδ C hemb hboundary hzero J}

/-- The coframe corrects the endomorphism away from the original interval. -/
def correctedField (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))
    (z : ℝ × (Model k × ℝ)) : (Model k × ℝ) →L[ℝ] (Model k × ℝ) :=
  P.toContinuousLinearMap.comp
    ((coframeComplexStructure ((c.coframe z).comp P.toContinuousLinearMap)).comp
      P.symm.toContinuousLinearMap)

theorem smooth_correctedField : ContDiffOn ℝ ∞ (c.correctedField P) c.domain :=
  contDiffOn_const.clm_comp
    ((contDiffOn_coframeComplexStructure (c.smooth_coframe.clm_comp contDiffOn_const)
      (fun z hz => (c.invertible_coframe z hz).comp ⟨P, rfl⟩)).clm_comp contDiffOn_const)

theorem correctedField_sq {z : ℝ × (Model k × ℝ)} (hz : z ∈ c.domain)
    (v : Model k × ℝ) : c.correctedField P z (c.correctedField P z v) = -v := by
  simp only [correctedField, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]
  rw [coframeComplexStructure_sq _ ((c.invertible_coframe z hz).comp ⟨P, rfl⟩)]
  simp

theorem normalized_correctedField (z : ℝ × (Model k × ℝ)) :
    P.symm.toContinuousLinearMap.comp ((c.correctedField P z).comp P.toContinuousLinearMap) =
      coframeComplexStructure ((c.coframe z).comp P.toContinuousLinearMap) := by
  ext v
  simp only [correctedField, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The correction agrees with the actual original chart endomorphism;
this matching equation is derived from the constructed coframe. -/
theorem correctedField_eq_original (s : Parameter) (w : Band δ (IntrinsicBoundary.Point k M))
    (hw : endBandCoordinates w ∈ (chartAt (Model k × ℝ) c.anchor).source)
    (hz : (s.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates w)) ∈ c.domain) :
    c.correctedField P (s.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates w)) =
      originalEndComplexInChart hδ C hemb hboundary hzero J c.anchor (s, w) := by
  let z := (s.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates w))
  let L := originalEndComplexInChart hδ C hemb hboundary hzero J c.anchor (s, w)
  have he : coframeComplexStructure ((c.coframe z).comp P.toContinuousLinearMap) =
      P.symm.toContinuousLinearMap.comp (L.comp P.toContinuousLinearMap) := by
    apply coframeComplexStructure_eq _ ((c.invertible_coframe z hz).comp ⟨P, rfl⟩)
    intro v
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using c.intertwines s w hw hz (P v)
  change P.toContinuousLinearMap.comp ((coframeComplexStructure
    ((c.coframe z).comp P.toContinuousLinearMap)).comp P.symm.toContinuousLinearMap) = L
  rw [he]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

include hC hinv in
/-- The scalar coordinate reconstructs every original tensor slot in the
consumer's actual spatial coordinates, including the inclusion differential. -/
theorem coordinate_reconstruction
    (σ : OriginalNativeCanonicalSection C J N)
    (s : Parameter) (w : Band δ (IntrinsicBoundary.Point k M))
    (hw : (s, w) ∈ c.baseDomain) (q : ℂ)
    (hq : q = c.tensorCoordinateLinearMap (N := N) (s, w) (originalEndSection C J N σ (s, w))) :
    q • coframeSquaredGenerator ((c.coframe (s.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates w))).comp
      P.toContinuousLinearMap) =
    ((originalNativeSectionTensor C J N σ s
      (cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) w)).compContinuousLinearMap
      (fun _ => (originalEndCanonicalDifferential hδ (C s) (hemb s) (hboundary s) (hzero s) c.anchor w).inverse)).compContinuousLinearMap
        (fun _ => P.toContinuousLinearMap) := by
  have hr := c.reconstruction (N := N) hC hinv hw
    (canonicalSquareMap _ (originalEndSection C J N σ (s, w)))
  rw [c.coefficient_squareMap, ← hq] at hr
  change _ = (((canonicalSquareMap _ (originalEndSection C J N σ (s, w))).val.compContinuousLinearMap
    (fun _ => N.symm.toContinuousLinearMap)).compContinuousLinearMap
      (fun _ => (originalEndCanonicalDifferential hδ (C s) (hemb s) (hboundary s) (hzero s) c.anchor w).inverse)).compContinuousLinearMap
        (fun _ => P.toContinuousLinearMap)
  rw [hr]
  have hi := isInvertible_originalEndCanonicalDifferential hδ (C s) (hemb s) (hC s)
    (hboundary s) (hinv s) (hzero s) c.anchor w hw.1.2
  ext v
  simp only [coframeSquaredGenerator, nativeCoframe, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, hi.self_apply_inverse]


include P hC hinv in
/-- A coefficient germ transfers to every chart of the same original
bundle by the derived real smooth transition, rather than by a new hypothesis. -/
theorem HasSectionCoefficientExtension.changeChart
    {σ : OriginalNativeCanonicalSection C J N} {p : Parameter × Band δ (IntrinsicBoundary.Point k M)}
    (hc : c.HasSectionCoefficientExtension (N := N) σ p) (hpc : p ∈ c.baseDomain)
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (hpd : p ∈ d.baseDomain) : d.HasSectionCoefficientExtension (N := N) σ p := by
  obtain ⟨U, q, hpU, hUc, hq, heq⟩ := hc
  let e := chartAt (Model k × ℝ) d.anchor
  let f := chartAt (Model k × ℝ) c.anchor
  let g := fun z : ℝ × (Model k × ℝ) => (z.1, f (e.symm z.2))
  have hg : ContDiffOn ℝ ∞ g (c.transitionDomain d) :=
    contDiffOn_fst.prodMk
      ((contDiffOn_originalEndCoordinateTransition d.anchor c.anchor).comp
        contDiffOn_snd (fun _ hz => hz.1.1.2))
  let V : TopologicalSpace.Opens (ℝ × (Model k × ℝ)) :=
    ⟨c.transitionDomain d ∩ g ⁻¹' U,
      hg.continuousOn.isOpen_inter_preimage (c.isOpen_transitionDomain d) U.isOpen⟩
  have hpcd : (p.1.val, e (endBandCoordinates p.2)) ∈ c.transitionDomain d := by
    refine ⟨⟨⟨mem_univ _, e.map_source hpd.1.2, ?_⟩, ?_⟩, hpd.2⟩
    · change e.symm (e (endBandCoordinates p.2)) ∈ f.source
      rw [e.left_inv hpd.1.2]
      exact hpc.1.2
    · change (p.1.val, f (e.symm (e (endBandCoordinates p.2)))) ∈ c.domain
      rw [e.left_inv hpd.1.2]
      exact hpc.2
  have hpV : (p.1.val, e (endBandCoordinates p.2)) ∈ V := by
    refine ⟨hpcd, ?_⟩
    change (p.1.val, f (e.symm (e (endBandCoordinates p.2)))) ∈ U
    rw [e.left_inv hpd.1.2]
    exact hpU
  refine ⟨V, fun z => c.transitionExtension (P := P) d z * q (g z), hpV,
    (fun _ hz => hz.1.2),
    ((c.smooth_transitionExtension (P := P) d).mono inter_subset_left).mul
      (hq.comp (hg.mono inter_subset_left) (fun _ hz => hz.2)), ?_⟩
  intro s w hw hz
  have hcw : endBandCoordinates w ∈ f.source := by
    have h := hz.1.1.1.2.2
    change e.symm (e (endBandCoordinates w)) ∈ f.source at h
    rwa [e.left_inv hw] at h
  have hU : (s.val, f (endBandCoordinates w)) ∈ U := by
    have h := hz.2
    change (s.val, f (e.symm (e (endBandCoordinates w)))) ∈ U at h
    rwa [e.left_inv hw] at h
  have hdw : (s, w) ∈ d.baseDomain := ⟨⟨mem_univ _, hw⟩, hz.1.2⟩
  have hcw' : (s, w) ∈ c.baseDomain := ⟨⟨mem_univ _, hcw⟩, hUc hU⟩
  have ht : c.transitionExtension (P := P) d (s.val, e (endBandCoordinates w)) = c.transition (N := N) d (s, w) := by
    dsimp only [transitionExtension]
    rw [e.left_inv hw]
    exact (originalEndCanonical_squaredTransition hδ (C s) (hemb s) (hC s)
      (hboundary s) (hinv s) (hzero s) N P d.anchor c.anchor w hw hcw _ _).symm
  change c.transitionExtension (P := P) d (s.val, e (endBandCoordinates w)) * q (s.val, f (e.symm (e (endBandCoordinates w)))) = _
  rw [e.left_inv hw, ht, heq s w hcw hU]
  exact (c.tensorCoordinateLinearMap_transition (N := N) hC hinv d ⟨hcw', hdw⟩ _).symm


include hC hinv in
/-- A local original scalar germ constructs a native graph and derives
its full tensor identity in the actual original inclusion/chart coordinates. -/
theorem exists_graphGerm_of_sectionCoefficient
    (σ : OriginalNativeCanonicalSection C J N)
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) (hp : p ∈ c.baseDomain)
    (hσ : c.HasSectionCoefficientExtension (N := N) σ p)
    (hnσ : originalEndSection C J N σ p ≠ 0) :
    ∃ g : NativeCoordinateCanonicalGraphGerm P
      (parameterInterval ×ˢ (univ : Set (Model k × ℝ)))
      (p.1.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates p.2)),
      ∀ (s : Parameter) (w : Band δ (IntrinsicBoundary.Point k M)),
        endBandCoordinates w ∈ (chartAt (Model k × ℝ) c.anchor).source →
        ∀ hw : (s.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates w)) ∈ g.domain,
          g.complexGerm.field (s.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates w)) =
            originalEndComplexInChart hδ C hemb hboundary hzero J c.anchor (s, w) ∧
          (canonicalSquareMap (g.patch.complex (g.bundleMap ⟨_, hw⟩).proj)
            (g.bundleMap ⟨_, hw⟩).snd).val =
            ((originalNativeSectionTensor C J N σ s
              (cylinder (fun z : Half δ (IntrinsicBoundary.Point k M) => C s z.val) w)).compContinuousLinearMap
              (fun _ => (originalEndCanonicalDifferential hδ (C s) (hemb s)
                (hboundary s) (hzero s) c.anchor w).inverse)).compContinuousLinearMap
              (fun _ => P.toContinuousLinearMap) := by
  obtain ⟨U, q, hpU, hUc, hq, heq⟩ := hσ
  let A := parameterInterval ×ˢ (univ : Set (Model k × ℝ))
  let z₀ := (p.1.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates p.2))
  let j : NativeCoordinateComplexGerm P A z₀ :=
    { domain := U
      mem_domain := hpU
      mem_locus := ⟨p.1.property, mem_univ _⟩
      field := c.correctedField P
      smooth_field := (c.smooth_correctedField P).mono hUc
      square := fun z hz => c.correctedField_sq P (hUc hz.1) }
  let b := j.bundlePatch
  have hbU : (b.domain : Set (ℝ × (Model k × ℝ))) ⊆ U := j.bundlePatch_subset
  have hbc : (b.domain : Set (ℝ × (Model k × ℝ))) ⊆ c.domain := hbU.trans hUc
  let S := fun z : ℝ × (Model k × ℝ) =>
    q z • coframeSquaredGenerator ((c.coframe z).comp P.toContinuousLinearMap)
  have hS : ContDiffOn ℝ ∞ S b.domain :=
    (hq.mono hbU).smul (contDiffOn_coframeSquaredGenerator
      ((c.smooth_coframe.mono hbc).clm_comp contDiffOn_const))
  have hcanonical : ∀ z, ∀ hz : z ∈ (b.domain : Set (ℝ × (Model k × ℝ))) ∩ A,
      IsSquaredCanonicalTensor (b.complex ⟨z, hz.1⟩) (S z) := by
    intro z hz
    rw [b.complex_eq hz.2]
    change IsSquaredCanonicalTensor
      (P.symm.toContinuousLinearMap.comp ((c.correctedField P z).comp P.toContinuousLinearMap)) (S z)
    rw [c.normalized_correctedField P]
    exact (squaredCanonicalSubmodule _).smul_mem (q z)
      (coframeSquaredGenerator_canonical _ _
        (coframeComplexStructure_intertwines _ ((c.invertible_coframe z (hbc hz.1)).comp ⟨P, rfl⟩)))
  have hnq : q z₀ ≠ 0 := by
    intro hzeroq
    apply hnσ
    apply (c.tensorCoordinateEquiv (N := N) hC hinv p hp).injective
    change c.tensorCoordinateLinearMap (N := N) p (originalEndSection C J N σ p) =
      c.tensorCoordinateLinearMap (N := N) p 0
    rw [map_zero, ← heq p.1 p.2 hp.1.2 hpU]
    exact hzeroq
  have hnS : S z₀ ≠ 0 := smul_ne_zero hnq
    (coframeSquaredGenerator_ne_zero _ ((c.invertible_coframe z₀ (hUc hpU)).comp ⟨P, rfl⟩))
  let R := fun z => canonicalCoframeCorrection (b.normalizedCoframe z) (S z)
  have hR : ContDiffOn ℝ ∞ R b.domain := contDiffOn_canonicalCoframeCorrection
    b.smooth_normalizedCoframe (fun z hz => b.invertible_normalizedCoframe hz) hS
  have hRc : ∀ z : b.domain, IsSquaredCanonicalTensor (b.complex z) (R z.val) :=
    fun z => canonicalCoframeCorrection_canonical _ _
      (coframeComplexStructure_intertwines _ (b.invertible_normalizedCoframe z.property)) _
  have hRe : ∀ z, ∀ hz : z ∈ (b.domain : Set (ℝ × (Model k × ℝ))) ∩ A, R z = S z :=
    fun z hz => canonicalCoframeCorrection_eq _ (b.invertible_normalizedCoframe hz.1)
      (b.complex ⟨z, hz.1⟩)
      (coframeComplexStructure_intertwines _ (b.invertible_normalizedCoframe hz.1)) _ (hcanonical z hz)
  let τ : ∀ z : b.domain, CanonicalTensorSquare (b.complex z) := fun z =>
    (canonicalSquareEquivOfComplexStructure _ (b.complex_sq z)).symm ⟨R z.val, hRc z⟩
  have hτ : ∀ z : b.domain, (canonicalSquareMap (b.complex z) (τ z)).val = R z.val :=
    fun z => congrArg Subtype.val ((canonicalSquareEquivOfComplexStructure _
      (b.complex_sq z)).apply_symm_apply _)
  have hsτ : b.IsSmoothSection τ := by
    apply (verticalCanonicalTensorSquareSection_smooth_iff b.smooth_complex b.complex_sq τ).mpr
    simp_rw [hτ]
    intro z
    exact contMDiffAt_subtype_iff.mpr
      (contMDiffAt_iff_contDiffAt.mpr (hR.contDiffAt (b.domain.isOpen.mem_nhds z.property)))
  have hnτ : τ ⟨z₀, j.mem_bundlePatch⟩ ≠ 0 := by
    intro hzeroτ
    have h := hτ ⟨z₀, j.mem_bundlePatch⟩
    rw [hzeroτ, map_zero, Submodule.coe_zero, hRe z₀ ⟨j.mem_bundlePatch, j.mem_locus⟩] at h
    exact hnS h.symm
  let g : NativeCoordinateCanonicalGraphGerm P A z₀ :=
    { complexGerm := j
      domain := b.domain
      subset_bundlePatch := Subset.refl _
      mem_domain := j.mem_bundlePatch
      bundleMap := fun z => ⟨z, τ z⟩
      smooth_bundleMap := hsτ
      projection_locus := fun _ _ => rfl
      nonzero_center := hnτ }
  refine ⟨g, ?_⟩
  intro s w hw hzw
  have hzA : (s.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates w)) ∈ A := ⟨s.property, mem_univ _⟩
  refine ⟨c.correctedField_eq_original P s w hw (hbc hzw), ?_⟩
  change (canonicalSquareMap (b.complex ⟨_, hzw⟩) (τ ⟨_, hzw⟩)).val = _
  rw [hτ, hRe _ ⟨hzw, hzA⟩]
  exact c.coordinate_reconstruction N P hC hinv σ s w
    ⟨⟨mem_univ _, hw⟩, hbc hzw⟩ _ (heq s w hw (hbU hzw))


end OriginalEndCanonicalChart
include P hC hinv in
/-- The original local coefficient convention is independent of the chart. -/
theorem originalEndSectionExtensions_of_local
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : HasOriginalEndLocalSectionExtensions hδ C hemb hboundary hzero J N σ) :
    HasOriginalEndSectionExtensions hδ C hemb hboundary hzero J N σ := by
  intro d p hpd
  obtain ⟨c, hpc, hc⟩ := hσ p
  exact OriginalEndCanonicalChart.HasSectionCoefficientExtension.changeChart
    (N := N) P hC hinv c hc hpc d hpd


/-- The source open-extension convention gives an actual smooth section of
the independently constructed original interval-end bundle. This is
only the forward implication, not an endpoint extension theorem for bare
boundary-manifold smoothness. -/
theorem contMDiff_originalEndSection
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : HasOriginalEndLocalSectionExtensions hδ C hemb hboundary hzero J N σ) :
    let a := originalEndCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero J N P hC hinv hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    ContMDiff (familyModel (k + 1)) ((familyModel (k + 1)).prod 𝓘(ℝ, ℂ)) ∞
      (fun p => (⟨p, originalEndSection C J N σ p⟩ : Bundle.TotalSpace ℂ
        (fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) =>
          CanonicalTensorSquare (originalEndComplex C J N p)))) := by
  dsimp only
  let a := originalEndCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero J N P hC hinv hJ hJsq
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  have hs := originalEndSectionExtensions_of_local hδ C hemb hboundary hzero J N P hC hinv σ hσ
  intro x
  rw [Bundle.contMDiffAt_section]
  let c := originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq x
  have hx : x ∈ c.baseDomain :=
    mem_originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq x
  obtain ⟨U, q, hxU, _, hq, heq⟩ := hs c x hx
  let e := chartAt (Model k × ℝ) c.anchor
  let z := fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) => (p.1.val, e (endBandCoordinates p.2))
  have ht : ContMDiffAt (familyModel (k + 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) => p.1.val) x :=
    contMDiff_subtypeVal_Icc.contMDiffAt.comp x contMDiffAt_fst
  have he : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) ∞
      (e ∘ endBandCoordinates) x.2 :=
    ((contMDiffOn_chart (I := 𝓘(ℝ, Model k × ℝ)) (x := c.anchor)).contMDiffAt
      (e.open_source.mem_nhds hx.1.2)).comp x.2 contMDiff_endBandCoordinates.contMDiffAt
  have hz : ContMDiffAt (familyModel (k + 1)) 𝓘(ℝ, ℝ × (Model k × ℝ)) ∞ z x :=
    ht.prodMk_space (he.comp x contMDiffAt_snd)
  have hqz := (contMDiffAt_iff_contDiffAt.mpr (hq.contDiffAt (U.isOpen.mem_nhds hxU))).comp x hz
  apply hqz.congr_of_eventuallyEq
  filter_upwards [(contMDiff_endBandCoordinates.continuous.comp continuous_snd).continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds hx.1.2),
    hz.continuousAt.preimage_mem_nhds (U.isOpen.mem_nhds hxU)] with p hpe hpU
  change c.tensorCoordinateLinearMap (N := N) p (originalEndSection C J N σ p) = q (z p)
  exact (heq p.1 p.2 hpe hpU).symm


include hC hinv in
/-- The original section, with the source's local smooth-extension convention,
produces the end graph extensions used by the completed-family grading
consumer. No target graph or tensor matching is an input. -/
theorem originalNativeEndGradingGraphExtensions
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : HasOriginalEndLocalSectionExtensions hδ C hemb hboundary hzero J N σ)
    (hnσ : ∀ s x, σ s x ≠ 0) :
    PairDeformation.HasNativeEndGradingGraphExtensions hδ C hemb hboundary hzero
      J (originalNativeSectionTensor C J N σ) P := by
  have hs := originalEndSectionExtensions_of_local hδ C hemb hboundary hzero J N P hC hinv σ hσ
  intro t x r hr
  let u : Band δ (IntrinsicBoundary.Point k M) := ⟨(-r, x), by
    refine ⟨?_, mem_univ _⟩
    change -r < δ
    linarith⟩
  let p : Parameter × Band δ (IntrinsicBoundary.Point k M) := (t, u)
  let c := originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq p
  have hp : p ∈ c.baseDomain :=
    mem_originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq p
  have ha : c.anchor = (x, r) := by
    have h := (exists_originalEndCanonicalChart hδ C hemb hboundary hzero J P hC hinv hJ hJsq p).choose_spec.1
    simpa only [c, originalEndCanonicalChartAt, p, u, endBandCoordinates, neg_neg] using h
  have h := c.exists_graphGerm_of_sectionCoefficient N P hC hinv σ p hp (hs c p hp)
    (hnσ p.1 (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C p.1 q.val) p.2))
  rw [ha] at h
  have hcoord : endBandCoordinates p.2 = (x, r) := by
    change (x, - -r) = (x, r)
    rw [neg_neg]
  rw [show p.1 = t from rfl, hcoord] at h
  obtain ⟨g, hg⟩ := h
  refine ⟨g, ?_⟩
  intro s w
  dsimp only
  intro hw hzw
  exact hg s w hw hzw


include hC hinv in
/-- The constructed original graph is consumed by the existing end
section-germ producer, retaining the original complex field and full tensor. -/
theorem originalNativeEndGradingSectionGerms
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J N)
    (hσ : HasOriginalEndLocalSectionExtensions hδ C hemb hboundary hzero J N σ)
    (hnσ : ∀ s x, σ s x ≠ 0) :
    PairDeformation.HasNativeEndGradingSectionGerms hδ C hemb hboundary hzero
      J (originalNativeSectionTensor C J N σ) P :=
  PairDeformation.nativeEndGradingSectionGerms_of_graphExtensions
    hδ C hemb hboundary hzero J (originalNativeSectionTensor C J N σ) P
    (originalNativeEndGradingGraphExtensions hδ C hemb hboundary hzero J N P hC hinv hJ hJsq σ hσ hnσ)


end FsFltz.Geometry.IntrinsicCompletionGluing
