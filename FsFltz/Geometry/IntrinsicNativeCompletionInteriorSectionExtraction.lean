import FsFltz.Geometry.IntrinsicNativeCompletionInteriorCanonicalBundle
import FsFltz.Geometry.IntrinsicNativeCompletionGradingGraphExtensions

/-!
# Original interior sections give grading graph extensions

Source: `geoemtric-part-fsf.tex`, lines 119–122 (open smooth extension),
`def:maslov`, lines 212–232, and `sec:lean`, lines 788–814. The source
section belongs to the original completion's canonical tensor-square fibers.
Its interior coefficients have local open smooth extensions in the independently
constructed original canonical bundle. Graphs and full tensor matching are
outputs. The cylindrical end and endpoint comparison laws are separate.
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
  (P : Model (2 * n) ≃L[ℝ] Model (k + 1))

variable
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)

/-- An original section of the native completed-fiber canonical square. -/
abbrev OriginalNativeCanonicalSection :=
  ∀ (s : Parameter) (x : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val)),
    CanonicalTensorSquare
      (P.symm.toContinuousLinearMap.comp ((J s x).comp P.toContinuousLinearMap))

/-- Restriction uses the original total family's interior inclusion. -/
def originalInteriorSection (σ : OriginalNativeCanonicalSection C J P)
    (p : Parameter × IntrinsicInterior.Point k M) :
    CanonicalTensorSquare (originalInteriorComplex C J P p) :=
  σ p.1 (interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C p.1 q.val) p.2)

/-- The full original tensor is natural square multiplication, expressed
back in the original native tangent. No tensor field is separately supplied. -/
def originalNativeSectionTensor (σ : OriginalNativeCanonicalSection C J P)
    (s : Parameter) (x : Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => Model (k + 1)) ℂ :=
  (canonicalSquareMap _ (σ s x)).val.compContinuousLinearMap
    (fun _ => P.symm.toContinuousLinearMap)

variable {hδ C hemb hboundary hzero J}

/-- A scalar germ in one original bundle chart, with the source's explicit
open-extension convention at interval endpoints. -/
def OriginalInteriorCanonicalChart.HasSectionCoefficientExtension
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (σ : OriginalNativeCanonicalSection C J P) (p : Parameter × IntrinsicInterior.Point k M) : Prop :=
  ∃ (U : TopologicalSpace.Opens (ℝ × Model (k + 1))) (q : (ℝ × Model (k + 1)) → ℂ),
    (p.1.val, chartAt (Model (k + 1)) c.anchor p.2) ∈ U ∧
    (U : Set (ℝ × Model (k + 1))) ⊆ c.domain ∧ ContDiffOn ℝ ∞ q U ∧
    ∀ (s : Parameter) (w : IntrinsicInterior.Point k M),
      w ∈ (chartAt (Model (k + 1)) c.anchor).source →
      (s.val, chartAt (Model (k + 1)) c.anchor w) ∈ U →
      q (s.val, chartAt (Model (k + 1)) c.anchor w) =
        c.tensorCoordinateLinearMap (P := P) (s, w) (originalInteriorSection C J P σ (s, w))

variable (hδ C hemb hboundary hzero J)

/-- Source smoothness asks for a coefficient germ in some original bundle
chart near each point; no selected target chart or graph is supplied. -/
def HasOriginalInteriorLocalSectionExtensions (σ : OriginalNativeCanonicalSection C J P) : Prop :=
  ∀ p : Parameter × IntrinsicInterior.Point k M,
    ∃ c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n),
      p ∈ c.baseDomain ∧ c.HasSectionCoefficientExtension (P := P) σ p

/-- All-chart form, derived below from the local source convention. -/
def HasOriginalInteriorSectionExtensions (σ : OriginalNativeCanonicalSection C J P) : Prop :=
  ∀ (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (p : Parameter × IntrinsicInterior.Point k M), p ∈ c.baseDomain →
    c.HasSectionCoefficientExtension (P := P) σ p

namespace OriginalInteriorCanonicalChart

variable (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
variable {hδ C hemb hboundary hzero J}

/-- The coframe corrects the endomorphism away from the original interval. -/
def correctedField (P : Model (2 * n) ≃L[ℝ] Model (k + 1))
    (z : ℝ × Model (k + 1)) : Model (k + 1) →L[ℝ] Model (k + 1) :=
  P.toContinuousLinearMap.comp
    ((coframeComplexStructure ((c.coframe z).comp P.toContinuousLinearMap)).comp
      P.symm.toContinuousLinearMap)

theorem smooth_correctedField : ContDiffOn ℝ ∞ (c.correctedField P) c.domain :=
  contDiffOn_const.clm_comp
    ((contDiffOn_coframeComplexStructure (c.smooth_coframe.clm_comp contDiffOn_const)
      (fun z hz => (c.invertible_coframe z hz).comp ⟨P, rfl⟩)).clm_comp contDiffOn_const)

theorem correctedField_sq {z : ℝ × Model (k + 1)} (hz : z ∈ c.domain)
    (v : Model (k + 1)) : c.correctedField P z (c.correctedField P z v) = -v := by
  simp only [correctedField, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]
  rw [coframeComplexStructure_sq _ ((c.invertible_coframe z hz).comp ⟨P, rfl⟩)]
  simp

theorem normalized_correctedField (z : ℝ × Model (k + 1)) :
    P.symm.toContinuousLinearMap.comp ((c.correctedField P z).comp P.toContinuousLinearMap) =
      coframeComplexStructure ((c.coframe z).comp P.toContinuousLinearMap) := by
  ext v
  simp only [correctedField, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The correction agrees with the actual original chart endomorphism;
this matching equation is derived from the constructed coframe. -/
theorem correctedField_eq_original (s : Parameter) (w : IntrinsicInterior.Point k M)
    (hw : w ∈ (chartAt (Model (k + 1)) c.anchor).source)
    (hz : (s.val, chartAt (Model (k + 1)) c.anchor w) ∈ c.domain) :
    c.correctedField P (s.val, chartAt (Model (k + 1)) c.anchor w) =
      originalInteriorComplexInChart hδ C hemb hboundary hzero J c.anchor (s, w) := by
  let z := (s.val, chartAt (Model (k + 1)) c.anchor w)
  let L := originalInteriorComplexInChart hδ C hemb hboundary hzero J c.anchor (s, w)
  have he : coframeComplexStructure ((c.coframe z).comp P.toContinuousLinearMap) =
      P.symm.toContinuousLinearMap.comp (L.comp P.toContinuousLinearMap) := by
    apply coframeComplexStructure_eq _ ((c.invertible_coframe z hz).comp ⟨P, rfl⟩)
    intro v
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using c.intertwines s w hw hz (P v)
  change P.toContinuousLinearMap.comp ((coframeComplexStructure
    ((c.coframe z).comp P.toContinuousLinearMap)).comp P.symm.toContinuousLinearMap) = L
  rw [he]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

include hC hinv in
/-- The scalar coordinate reconstructs every original tensor slot in the
consumer's actual spatial coordinates, including the inclusion differential. -/
theorem coordinate_reconstruction
    (σ : OriginalNativeCanonicalSection C J P)
    (s : Parameter) (w : IntrinsicInterior.Point k M)
    (hw : (s, w) ∈ c.baseDomain) (q : ℂ)
    (hq : q = c.tensorCoordinateLinearMap (P := P) (s, w) (originalInteriorSection C J P σ (s, w))) :
    q • coframeSquaredGenerator ((c.coframe (s.val, chartAt (Model (k + 1)) c.anchor w)).comp
      P.toContinuousLinearMap) =
    ((originalNativeSectionTensor C J P σ s
      (interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) w)).compContinuousLinearMap
      (fun _ => (originalInteriorCanonicalDifferential hδ (C s) (hemb s) (hboundary s) (hzero s) c.anchor w).inverse)).compContinuousLinearMap
        (fun _ => P.toContinuousLinearMap) := by
  have hr := c.reconstruction (P := P) hC hinv hw
    (canonicalSquareMap _ (originalInteriorSection C J P σ (s, w)))
  rw [c.coefficient_squareMap, ← hq] at hr
  change _ = (((canonicalSquareMap _ (originalInteriorSection C J P σ (s, w))).val.compContinuousLinearMap
    (fun _ => P.symm.toContinuousLinearMap)).compContinuousLinearMap (fun _ => _)).compContinuousLinearMap _
  rw [hr]
  have hi := isInvertible_originalInteriorCanonicalDifferential hδ (C s) (hemb s) (hC s)
    (hboundary s) (hinv s) (hzero s) c.anchor w hw.1.2
  ext v
  simp only [coframeSquaredGenerator, nativeCoframe, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, hi.self_apply_inverse]


include hC hinv in
/-- A coefficient germ transfers to every chart of the same original
bundle by the derived real smooth transition, rather than by a new hypothesis. -/
theorem HasSectionCoefficientExtension.changeChart
    {σ : OriginalNativeCanonicalSection C J P} {p : Parameter × IntrinsicInterior.Point k M}
    (hc : c.HasSectionCoefficientExtension (P := P) σ p) (hpc : p ∈ c.baseDomain)
    (d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (hpd : p ∈ d.baseDomain) : d.HasSectionCoefficientExtension (P := P) σ p := by
  obtain ⟨U, q, hpU, hUc, hq, heq⟩ := hc
  let e := chartAt (Model (k + 1)) d.anchor
  let f := chartAt (Model (k + 1)) c.anchor
  let g := fun z : ℝ × Model (k + 1) => (z.1, f (e.symm z.2))
  have hg : ContDiffOn ℝ ∞ g (c.transitionDomain d) :=
    contDiffOn_fst.prodMk
      ((contDiffOn_originalInteriorCoordinateTransition d.anchor c.anchor).comp
        contDiffOn_snd (fun _ hz => hz.1.1.2))
  let V : TopologicalSpace.Opens (ℝ × Model (k + 1)) :=
    ⟨c.transitionDomain d ∩ g ⁻¹' U,
      hg.continuousOn.isOpen_inter_preimage (c.isOpen_transitionDomain d) U.isOpen⟩
  have hpcd : (p.1.val, e p.2) ∈ c.transitionDomain d := by
    refine ⟨⟨⟨mem_univ _, e.map_source hpd.1.2, ?_⟩, ?_⟩, hpd.2⟩
    · change e.symm (e p.2) ∈ f.source
      rw [e.left_inv hpd.1.2]
      exact hpc.1.2
    · change (p.1.val, f (e.symm (e p.2))) ∈ c.domain
      rw [e.left_inv hpd.1.2]
      exact hpc.2
  have hpV : (p.1.val, e p.2) ∈ V := by
    refine ⟨hpcd, ?_⟩
    change (p.1.val, f (e.symm (e p.2))) ∈ U
    rw [e.left_inv hpd.1.2]
    exact hpU
  refine ⟨V, fun z => c.transitionExtension (P := P) d z * q (g z), hpV,
    (fun _ hz => hz.1.2),
    ((c.smooth_transitionExtension (P := P) d).mono inter_subset_left).mul
      (hq.comp (hg.mono inter_subset_left) (fun _ hz => hz.2)), ?_⟩
  intro s w hw hz
  have hcw : w ∈ f.source := by
    have h := hz.1.1.1.2.2
    change e.symm (e w) ∈ f.source at h
    rwa [e.left_inv hw] at h
  have hU : (s.val, f w) ∈ U := by
    have h := hz.2
    change (s.val, f (e.symm (e w))) ∈ U at h
    rwa [e.left_inv hw] at h
  have hdw : (s, w) ∈ d.baseDomain := ⟨⟨mem_univ _, hw⟩, hz.1.2⟩
  have hcw' : (s, w) ∈ c.baseDomain := ⟨⟨mem_univ _, hcw⟩, hUc hU⟩
  have ht : c.transitionExtension (P := P) d (s.val, e w) = c.transition (P := P) d (s, w) := by
    dsimp only [transitionExtension]
    rw [e.left_inv hw]
    exact (originalInteriorCanonical_squaredTransition hδ (C s) (hemb s) (hC s)
      (hboundary s) (hinv s) (hzero s) P d.anchor c.anchor w hw hcw _ _).symm
  change c.transitionExtension (P := P) d (s.val, e w) * q (s.val, f (e.symm (e w))) = _
  rw [e.left_inv hw, ht, heq s w hcw hU]
  exact (c.tensorCoordinateLinearMap_transition (P := P) hC hinv d ⟨hcw', hdw⟩ _).symm


include hC hinv in
/-- A local original scalar germ constructs a native graph and derives
its full tensor identity in the actual original inclusion/chart coordinates. -/
theorem exists_graphGerm_of_sectionCoefficient
    (σ : OriginalNativeCanonicalSection C J P)
    (p : Parameter × IntrinsicInterior.Point k M) (hp : p ∈ c.baseDomain)
    (hσ : c.HasSectionCoefficientExtension (P := P) σ p)
    (hnσ : originalInteriorSection C J P σ p ≠ 0) :
    ∃ g : NativeCoordinateCanonicalGraphGerm P
      (parameterInterval ×ˢ (univ : Set (Model (k + 1))))
      (p.1.val, chartAt (Model (k + 1)) c.anchor p.2),
      ∀ (s : Parameter) (w : IntrinsicInterior.Point k M),
        w ∈ (chartAt (Model (k + 1)) c.anchor).source →
        ∀ hw : (s.val, chartAt (Model (k + 1)) c.anchor w) ∈ g.domain,
          g.complexGerm.field (s.val, chartAt (Model (k + 1)) c.anchor w) =
            originalInteriorComplexInChart hδ C hemb hboundary hzero J c.anchor (s, w) ∧
          (canonicalSquareMap (g.patch.complex (g.bundleMap ⟨_, hw⟩).proj)
            (g.bundleMap ⟨_, hw⟩).snd).val =
            ((originalNativeSectionTensor C J P σ s
              (interiorIn (fun z : Half δ (IntrinsicBoundary.Point k M) => C s z.val) w)).compContinuousLinearMap
              (fun _ => (originalInteriorCanonicalDifferential hδ (C s) (hemb s)
                (hboundary s) (hzero s) c.anchor w).inverse)).compContinuousLinearMap
              (fun _ => P.toContinuousLinearMap) := by
  obtain ⟨U, q, hpU, hUc, hq, heq⟩ := hσ
  let A := parameterInterval ×ˢ (univ : Set (Model (k + 1)))
  let z₀ := (p.1.val, chartAt (Model (k + 1)) c.anchor p.2)
  let j : NativeCoordinateComplexGerm P A z₀ :=
    { domain := U
      mem_domain := hpU
      mem_locus := ⟨p.1.property, mem_univ _⟩
      field := c.correctedField P
      smooth_field := (c.smooth_correctedField P).mono hUc
      square := fun z hz => c.correctedField_sq P (hUc hz.1) }
  let b := j.bundlePatch
  have hbU : (b.domain : Set (ℝ × Model (k + 1))) ⊆ U := j.bundlePatch_subset
  have hbc : (b.domain : Set (ℝ × Model (k + 1))) ⊆ c.domain := hbU.trans hUc
  let S := fun z : ℝ × Model (k + 1) =>
    q z • coframeSquaredGenerator ((c.coframe z).comp P.toContinuousLinearMap)
  have hS : ContDiffOn ℝ ∞ S b.domain :=
    (hq.mono hbU).smul (contDiffOn_coframeSquaredGenerator
      ((c.smooth_coframe.mono hbc).clm_comp contDiffOn_const))
  have hcanonical : ∀ z, ∀ hz : z ∈ (b.domain : Set (ℝ × Model (k + 1))) ∩ A,
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
    apply (c.tensorCoordinateEquiv (P := P) hC hinv p hp).injective
    change c.tensorCoordinateLinearMap p (originalInteriorSection C J P σ p) =
      c.tensorCoordinateLinearMap p 0
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
  have hRe : ∀ z, ∀ hz : z ∈ (b.domain : Set (ℝ × Model (k + 1))) ∩ A, R z = S z :=
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
  have hzA : (s.val, chartAt (Model (k + 1)) c.anchor w) ∈ A := ⟨s.property, mem_univ _⟩
  refine ⟨c.correctedField_eq_original P s w hw (hbc hzw), ?_⟩
  change (canonicalSquareMap (b.complex ⟨_, hzw⟩) (τ ⟨_, hzw⟩)).val = _
  rw [hτ, hRe _ ⟨hzw, hzA⟩]
  exact c.coordinate_reconstruction P hC hinv σ s w
    ⟨⟨mem_univ _, hw⟩, hbc hzw⟩ _ (heq s w hw (hbU hzw))


end OriginalInteriorCanonicalChart
include hC hinv in
/-- The original local coefficient convention is independent of the chart. -/
theorem originalInteriorSectionExtensions_of_local
    (σ : OriginalNativeCanonicalSection C J P)
    (hσ : HasOriginalInteriorLocalSectionExtensions hδ C hemb hboundary hzero J P σ) :
    HasOriginalInteriorSectionExtensions hδ C hemb hboundary hzero J P σ := by
  intro d p hpd
  obtain ⟨c, hpc, hc⟩ := hσ p
  exact OriginalInteriorCanonicalChart.HasSectionCoefficientExtension.changeChart
    (P := P) hC hinv c hc hpc d hpd


/-- The source open-extension convention gives an actual smooth section of
the independently constructed original interval-interior bundle. This is
only the forward implication, not an endpoint extension theorem for bare
boundary-manifold smoothness. -/
theorem contMDiff_originalInteriorSection
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J P)
    (hσ : HasOriginalInteriorLocalSectionExtensions hδ C hemb hboundary hzero J P σ) :
    let a := originalInteriorCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero J P hC hinv hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    ContMDiff (familyModel (k + 1)) ((familyModel (k + 1)).prod 𝓘(ℝ, ℂ)) ∞
      (fun p => (⟨p, originalInteriorSection C J P σ p⟩ : Bundle.TotalSpace ℂ
        (fun p : Parameter × IntrinsicInterior.Point k M =>
          CanonicalTensorSquare (originalInteriorComplex C J P p)))) := by
  dsimp only
  let a := originalInteriorCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero J P hC hinv hJ hJsq
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  have hs := originalInteriorSectionExtensions_of_local hδ C hemb hboundary hzero J P hC hinv σ hσ
  intro x
  rw [Bundle.contMDiffAt_section]
  let c := originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq x
  have hx : x ∈ c.baseDomain :=
    mem_originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq x
  obtain ⟨U, q, hxU, _, hq, heq⟩ := hs c x hx
  let e := chartAt (Model (k + 1)) c.anchor
  let z := fun p : Parameter × IntrinsicInterior.Point k M => (p.1.val, e p.2)
  have ht : ContMDiffAt (familyModel (k + 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : Parameter × IntrinsicInterior.Point k M => p.1.val) x :=
    contMDiff_subtypeVal_Icc.contMDiffAt.comp x contMDiffAt_fst
  have he : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ e x.2 :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model (k + 1))) (x := c.anchor)).contMDiffAt
      (e.open_source.mem_nhds hx.1.2)
  have hz : ContMDiffAt (familyModel (k + 1)) 𝓘(ℝ, ℝ × Model (k + 1)) ∞ z x :=
    ht.prodMk_space (he.comp x contMDiffAt_snd)
  have hqz := (contMDiffAt_iff_contDiffAt.mpr (hq.contDiffAt (U.isOpen.mem_nhds hxU))).comp x hz
  apply hqz.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hx.1.2),
    hz.continuousAt.preimage_mem_nhds (U.isOpen.mem_nhds hxU)] with p hpe hpU
  change c.tensorCoordinateLinearMap p (originalInteriorSection C J P σ p) = q (z p)
  exact (heq p.1 p.2 hpe hpU).symm


include hC hinv in
/-- The original section, with the source's local smooth-extension convention,
produces the interior graph extensions used by the completed-family grading
consumer. No target graph or tensor matching is an input. -/
theorem originalNativeInteriorGradingGraphExtensions
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J P)
    (hσ : HasOriginalInteriorLocalSectionExtensions hδ C hemb hboundary hzero J P σ)
    (hnσ : ∀ s x, σ s x ≠ 0) :
    PairDeformation.HasNativeInteriorGradingGraphExtensions hδ C hemb hboundary hzero
      J (originalNativeSectionTensor C J P σ) P := by
  have hs := originalInteriorSectionExtensions_of_local hδ C hemb hboundary hzero J P hC hinv σ hσ
  intro t u
  let p : Parameter × IntrinsicInterior.Point k M := (t, u)
  let c := originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq p
  have hp : p ∈ c.baseDomain :=
    mem_originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq p
  have ha : c.anchor = u :=
    (exists_originalInteriorCanonicalChart hδ C hemb hboundary hzero J P hC hinv hJ hJsq p).choose_spec.1
  have h := c.exists_graphGerm_of_sectionCoefficient P hC hinv σ p hp (hs c p hp)
    (hnσ p.1 (interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C p.1 q.val) p.2))
  rw [ha] at h
  obtain ⟨g, hg⟩ := h
  exact ⟨g, hg⟩

include hC hinv in
/-- The constructed original graph is consumed by the existing interior
section-germ producer, retaining the original complex field and full tensor. -/
theorem originalNativeInteriorGradingSectionGerms
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (σ : OriginalNativeCanonicalSection C J P)
    (hσ : HasOriginalInteriorLocalSectionExtensions hδ C hemb hboundary hzero J P σ)
    (hnσ : ∀ s x, σ s x ≠ 0) :
    PairDeformation.HasNativeInteriorGradingSectionGerms hδ C hemb hboundary hzero
      J (originalNativeSectionTensor C J P σ) P :=
  PairDeformation.nativeInteriorGradingSectionGerms_of_graphExtensions
    hδ C hemb hboundary hzero J (originalNativeSectionTensor C J P σ) P
    (originalNativeInteriorGradingGraphExtensions hδ C hemb hboundary hzero J P hC hinv hJ hJsq σ hσ hnσ)


end FsFltz.Geometry.IntrinsicCompletionGluing
