import FsFltz.Geometry.IntrinsicNativeCompletionMixedCanonicalChart

/-!
# Reverse real mixed canonical transition germs

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 788–814. The inverse of the original real collar germ
provides smooth interior-to-end transitions across real parameter
neighborhoods. Their spatial derivatives are obtained by differentiating
the actual attachment maps, retaining the inward-time/outward-radius sign.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] {δ : ℝ}

local instance reverseMixedTransitionBandCharts : ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ
local instance reverseMixedTransitionProductCharts : ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
local instance reverseMixedTransitionProductSmooth : IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

section Slice

variable (hδ : 0 < δ)
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

include hC hinv in
/-- The reverse mixed differential follows from equality of the literal
attachment maps on a neighborhood of the interior point. -/
theorem originalReverseMixedCanonicalDifferential_of_germ
    (a : IntrinsicInterior.Point k M) (b : IntrinsicBoundary.Point k M × ℝ)
    (w : IntrinsicInterior.Point k M) (p : Band δ (IntrinsicBoundary.Point k M))
    (F : Model (k + 1) → Band δ (IntrinsicBoundary.Point k M))
    (hF : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ F
      (chartAt (Model (k + 1)) a w))
    (hFp : F (chartAt (Model (k + 1)) a w) = p)
    (ha : w ∈ (chartAt (Model (k + 1)) a).source)
    (hb : endBandCoordinates p ∈ (chartAt (Model k × ℝ) b).source)
    (heq : ∀ᶠ v in 𝓝 w,
      cylinder (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val)
        (F (chartAt (Model (k + 1)) a v)) =
      interiorIn (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) v) :
    originalEndCanonicalDifferential hδ C hemb hboundary hzero b p =
      (fderiv ℝ ((chartAt (Model k × ℝ) b) ∘ endBandCoordinates ∘ F)
        (chartAt (Model (k + 1)) a w)).comp
          (originalInteriorCanonicalDifferential hδ C hemb hboundary hzero a w) := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  let i := interiorIn (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val)
  let j := cylinder (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val)
  let ei := chartAt (Model (k + 1)) a
  let ee := chartAt (Model k × ℝ) b
  let B : Model (k + 1) →L[ℝ] (Model k × ℝ) := (originalEndChartDifferential b (endBandCoordinates p)).comp
    (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) endBandCoordinates p)
  have hi := isInvertible_mfderiv_completionInterior hδ C hemb hC hboundary hinv hzero w
  have hj := isInvertible_mfderiv_completionCylinder hδ C hemb hC hboundary hinv hzero p
  have hdF := hF.mdifferentiableAt (by simp)
  have hdJ := (contMDiff_cylinder hδ C hemb hC hboundary hinv hzero).mdifferentiableAt
    (by simp) (x := p)
  have hdEi := (mdifferentiable_chart (I := 𝓘(ℝ, Model (k + 1))) a).mdifferentiableAt ha
  have hdE := contMDiff_endBandCoordinates.mdifferentiableAt (by simp) (x := p)
  have hdEe := (mdifferentiable_chart (I := 𝓘(ℝ, Model k × ℝ)) b).mdifferentiableAt hb
  have hchain : (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p).comp
      ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) F (ei w)).comp
        (originalInteriorChartDifferential a w)) =
      mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) i w := by
    have hnear : j ∘ F ∘ ei =ᶠ[𝓝 w] i := heq
    have h := hnear.mfderiv_eq (I := 𝓘(ℝ, Model (k + 1)))
      (I' := 𝓘(ℝ, Model (k + 1)))
    have hdJ' : MDifferentiableAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
        j ((F ∘ ei) w) := by simpa only [Function.comp_apply, ei, hFp] using hdJ
    rw [mfderiv_comp w hdJ' (hdF.comp w hdEi), mfderiv_comp w hdF hdEi] at h
    dsimp only [Function.comp_apply] at h
    rw [hFp] at h
    exact h
  have hd : fderiv ℝ (ee ∘ endBandCoordinates ∘ F) (ei w) =
      B.comp (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) F (ei w)) := by
    rw [← mfderiv_eq_fderiv]
    have hdEE : MDifferentiableAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ)
        (ee ∘ endBandCoordinates) (F (ei w)) := by
      simpa only [ei, hFp] using hdEe.comp p hdE
    have h := mfderiv_comp (ei w) hdEE hdF
    rw [show F (ei w) = p from hFp, mfderiv_comp p hdEe hdE] at h
    exact h
  have hcancel : (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) F (ei w)).comp
      (originalInteriorChartDifferential a w) =
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p).inverse.comp
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) i w) := by
    rw [← hchain]
    ext v
    exact (hj.inverse_apply_self _).symm
  rw [hd]
  change B.comp (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p).inverse =
    (B.comp (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) F (ei w))).comp
      ((originalInteriorChartDifferential a w).comp
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) i w).inverse)
  apply ContinuousLinearMap.ext
  intro v
  have hc := congrArg (fun D : Model (k + 1) →L[ℝ] Model (k + 1) =>
    D ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) i w).inverse v)) hcancel
  change (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) F (ei w))
      ((originalInteriorChartDifferential a w)
        ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) i w).inverse v)) =
    (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p).inverse
      ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) i w)
        ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) i w).inverse v)) at hc
  rw [hi.self_apply_inverse] at hc
  exact congrArg B hc.symm

include hC hinv in
/-- The reverse actual spatial differential cancels from the determinant
square, using interior spatial normalization. -/
theorem originalReverseMixedCanonical_squaredTransition_of_germ
    (N : Model (2 * n) ≃L[ℝ] Model (k + 1))
    (a : IntrinsicInterior.Point k M) (b : IntrinsicBoundary.Point k M × ℝ)
    (w : IntrinsicInterior.Point k M) (p : Band δ (IntrinsicBoundary.Point k M))
    (F : Model (k + 1) → Band δ (IntrinsicBoundary.Point k M))
    (hF : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ F
      (chartAt (Model (k + 1)) a w))
    (hFp : F (chartAt (Model (k + 1)) a w) = p)
    (ha : w ∈ (chartAt (Model (k + 1)) a).source)
    (hb : endBandCoordinates p ∈ (chartAt (Model k × ℝ) b).source)
    (heq : ∀ᶠ v in 𝓝 w,
      cylinder (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val)
        (F (chartAt (Model (k + 1)) a v)) =
      interiorIn (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) v)
    (CI : Model (k + 1) →L[ℝ] TangentCoordinates n)
    (CE : (Model k × ℝ) →L[ℝ] TangentCoordinates n) :
    squaredCoframeTransition
      ((CE.comp (originalEndCanonicalDifferential hδ C hemb hboundary hzero b p)).comp N.toContinuousLinearMap)
      ((CI.comp (originalInteriorCanonicalDifferential hδ C hemb hboundary hzero a w)).comp N.toContinuousLinearMap) =
    squaredCoframeTransition
      ((CE.comp (fderiv ℝ ((chartAt (Model k × ℝ) b) ∘ endBandCoordinates ∘ F)
        (chartAt (Model (k + 1)) a w))).comp N.toContinuousLinearMap)
      (CI.comp N.toContinuousLinearMap) := by
  let HI := originalInteriorCanonicalDifferential hδ C hemb hboundary hzero a w
  let HE := originalEndCanonicalDifferential hδ C hemb hboundary hzero b p
  let L := fderiv ℝ ((chartAt (Model k × ℝ) b) ∘ endBandCoordinates ∘ F)
    (chartAt (Model (k + 1)) a w)
  have hHI : HI.IsInvertible :=
    isInvertible_originalInteriorCanonicalDifferential hδ C hemb hC hboundary hinv hzero a w ha
  have hHE : HE = L.comp HI := originalReverseMixedCanonicalDifferential_of_germ
    hδ C hemb hC hboundary hinv hzero a b w p F hF hFp ha hb heq
  let A := N.symm.toContinuousLinearMap.comp (HI.comp N.toContinuousLinearMap)
  have hA : A.IsInvertible :=
    (show N.symm.toContinuousLinearMap.IsInvertible from ⟨N.symm, rfl⟩).comp
      (hHI.comp ⟨N, rfl⟩)
  have h := squaredCoframeTransition_comp ((CE.comp L).comp N.toContinuousLinearMap)
    (CI.comp N.toContinuousLinearMap) A hA
  change squaredCoframeTransition ((CE.comp HE).comp N.toContinuousLinearMap)
    ((CI.comp HI).comp N.toContinuousLinearMap) = _
  rw [hHE]
  convert h using 1
  · congr 1 <;> ext v <;>
      simp only [A, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply]

end Slice

variable (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)
  (hzero : ∀ t b, C t (0, b) = b.val)
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hmix : HasRealMixedGerms (δ := δ) C)
  (J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (N : Model (2 * n) ≃L[ℝ] Model (k + 1))

include hC hinv hjoint hmix in
/-- The inverse real mixed collar germ supplies the reverse canonical-square
transition on an open real neighborhood, including parameter endpoints. -/
theorem exists_originalInteriorToEndCanonicalTransitionGerm
    (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (s : Parameter) (w : IntrinsicInterior.Point k M) (p : Band δ (IntrinsicBoundary.Point k M))
    (hpoint : totalInterior (fun t p => C t p.val) (s, w) =
      totalCylinder (fun t p => C t p.val) (s, p))
    (hw : (s, w) ∈ c.baseDomain) (hp : (s, p) ∈ d.baseDomain) :
    ∃ (U : TopologicalSpace.Opens (ℝ × Model (k + 1)))
      (g : ℝ × Model (k + 1) → Model k × ℝ) (f : ℝ × Model (k + 1) → ℂ),
      (s.val, chartAt (Model (k + 1)) c.anchor w) ∈ U ∧
      ContDiffOn ℝ ∞ g U ∧ ContDiffOn ℝ ∞ f U ∧
      g (s.val, chartAt (Model (k + 1)) c.anchor w) =
        chartAt (Model k × ℝ) d.anchor (endBandCoordinates p) ∧
      (U : Set (ℝ × Model (k + 1))) ⊆ (c.domain : Set (ℝ × Model (k + 1))) ∧
      (∀ z ∈ U, (z.1, g z) ∈ d.domain) ∧
      ∀ (t : Parameter) (v : IntrinsicInterior.Point k M),
        v ∈ (chartAt (Model (k + 1)) c.anchor).source →
        (t.val, chartAt (Model (k + 1)) c.anchor v) ∈ U →
        ∃ q : Band δ (IntrinsicBoundary.Point k M),
          endBandCoordinates q ∈ (chartAt (Model k × ℝ) d.anchor).source ∧
          chartAt (Model k × ℝ) d.anchor (endBandCoordinates q) =
            g (t.val, chartAt (Model (k + 1)) c.anchor v) ∧
          totalInterior (fun t p => C t p.val) (t, v) =
            totalCylinder (fun t p => C t p.val) (t, q) ∧
          f (t.val, chartAt (Model (k + 1)) c.anchor v) =
            squaredCoframeTransition (d.nativeCoframe N (t, q)) (c.nativeCoframe N (t, v)) := by
  classical
  let ei := chartAt (Model (k + 1)) c.anchor
  let ee := chartAt (Model k × ℝ) d.anchor
  obtain ⟨_, hpos, _⟩ := (totalInterior_eq_totalCylinder_iff
    (fun t p => C t p.val) hboundary (s, w) (s, p)).mp hpoint
  obtain ⟨A, hpA, hApos, hparam, _, hforward, hreverse⟩ :=
    hmix s p.val ⟨hpos, p.property.1⟩
  have hAw : (A (s.val, p.val)).2 = w := by
    have h : totalInterior (δ := δ) (fun t p => C t p.val) (s, (A (s.val, p.val)).2) =
        totalInterior (δ := δ) (fun t p => C t p.val) (s, w) :=
      (hforward s p hpA).trans hpoint.symm
    exact congrArg Prod.snd
      ((isOpenEmbedding_totalInterior hδ (fun t p => C t p.val) hzero hjoint).injective h)
  have hAfull : A (s.val, p.val) = (s.val, w) := Prod.ext (hparam _ hpA) hAw
  have hwA : (s.val, w) ∈ A.target := hAfull ▸ A.map_source hpA
  let R : ℝ × Model (k + 1) → ℝ × IntrinsicInterior.Point k M :=
    fun z => (z.1, ei.symm z.2)
  let U₀ : Set (ℝ × Model (k + 1)) := univ ×ˢ ei.target
  have hU₀ : IsOpen U₀ := isOpen_univ.prod ei.open_target
  have hR : ContMDiffOn 𝓘(ℝ, ℝ × Model (k + 1))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) ∞ R U₀ :=
    contDiffOn_fst.contMDiffOn.prodMk
      ((contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (k + 1))) (x := c.anchor)).comp
        contDiffOn_snd.contMDiffOn (fun _ hz => hz.2))
  let S₀ := U₀ ∩ R ⁻¹' A.target
  have hS₀ : IsOpen S₀ := hR.continuousOn.isOpen_inter_preimage hU₀ A.open_target
  let K : ℝ × Model (k + 1) → ℝ × IntrinsicBoundary.Point k M :=
    fun z => (A.symm (R z)).2
  have hK : ContMDiffOn 𝓘(ℝ, ℝ × Model (k + 1))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞ K S₀ :=
    contMDiff_snd.comp_contMDiffOn
      (A.contMDiffOn_invFun.comp (hR.mono inter_subset_left) inter_subset_right)
  let E : ℝ × Model (k + 1) → IntrinsicBoundary.Point k M × ℝ :=
    fun z => ((K z).2, -(K z).1)
  have hE : ContMDiffOn 𝓘(ℝ, ℝ × Model (k + 1)) 𝓘(ℝ, Model k × ℝ) ∞ E S₀ := by
    rw [modelWithCornersSelf_prod]
    exact (contMDiff_snd.comp_contMDiffOn hK).prodMk
      (contMDiff_fst.comp_contMDiffOn hK).neg
  let S := S₀ ∩ E ⁻¹' ee.source
  have hS : IsOpen S := hE.continuousOn.isOpen_inter_preimage hS₀ ee.open_source
  let g : ℝ × Model (k + 1) → Model k × ℝ := fun z => ee (E z)
  have hg : ContDiffOn ℝ ∞ g S :=
    ((contMDiffOn_chart (I := 𝓘(ℝ, Model k × ℝ)) (x := d.anchor)).comp
      (hE.mono inter_subset_left) inter_subset_right).contDiffOn
  let Z := S ∩ c.domain
  have hZ : IsOpen Z := hS.inter c.domain.isOpen
  let V := Z ∩ (fun z => (z.1, g z)) ⁻¹' d.domain
  have hV : IsOpen V := (continuous_fst.continuousOn.prodMk
    (hg.mono inter_subset_left).continuousOn).isOpen_inter_preimage hZ d.domain.isOpen
  let U : TopologicalSpace.Opens (ℝ × Model (k + 1)) := ⟨V, hV⟩
  let z₀ := (s.val, ei w)
  have hR₀ : R z₀ = (s.val, w) := by
    dsimp only [R, z₀]
    rw [ei.left_inv hw.1.2]
  have hK₀ : K z₀ = p.val := by
    dsimp only [K]
    rw [hR₀, ← hAfull]
    exact congrArg Prod.snd (A.toPartialEquiv.left_inv hpA)
  have hE₀ : E z₀ = endBandCoordinates p := by
    dsimp only [E]
    rw [hK₀]
    rfl
  have hz₀ : z₀ ∈ U := by
    refine ⟨⟨⟨⟨⟨mem_univ _, ei.map_source hw.1.2⟩, ?_⟩, ?_⟩, hw.2⟩, ?_⟩
    · change R z₀ ∈ A.target
      rw [hR₀]; exact hwA
    · change E z₀ ∈ ee.source
      rw [hE₀]; exact hp.1.2
    · change (s.val, ee (E z₀)) ∈ d.domain
      rw [hE₀]; exact hp.2
  let Q : ℝ × Model (k + 1) → Band δ (IntrinsicBoundary.Point k M) :=
    fun z => if h : K z ∈ Band δ (IntrinsicBoundary.Point k M) then ⟨K z, h⟩ else p
  have hQval : ∀ z ∈ S₀, (Q z).val = K z := by
    intro z hz
    have hband : K z ∈ Band δ (IntrinsicBoundary.Point k M) :=
      ⟨(hApos _ (A.map_target hz.2)).2, mem_univ _⟩
    simp only [Q, hband, dite_true]
  have hQ : ∀ z ∈ S₀,
      ContMDiffAt 𝓘(ℝ, ℝ × Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ Q z := by
    intro z hz
    apply contMDiffAt_band_iff_val.mpr
    have heq : Subtype.val ∘ Q =ᶠ[𝓝 z] K := by
      filter_upwards [hS₀.mem_nhds hz] with z' hz'
      exact hQval z' hz'
    exact (hK.contMDiffAt (hS₀.mem_nhds hz)).congr_of_eventuallyEq heq
  let f : ℝ × Model (k + 1) → ℂ := fun z =>
    squaredCoframeTransition
      (((d.coframe (z.1, g z)).comp (mixedSpatialDerivative g z)).comp N.toContinuousLinearMap)
      ((c.coframe z).comp N.toContinuousLinearMap)
  have hgU : ContDiffOn ℝ ∞ g U := hg.mono (fun _ hz => hz.1.1)
  have hf : ContDiffOn ℝ ∞ f U :=
    contDiffOn_squaredCoframeTransition
      (((d.smooth_coframe.comp (contDiffOn_fst.prodMk hgU) (fun _ hz => hz.2)).clm_comp
        (contDiffOn_mixedSpatialDerivative hgU U.isOpen)).clm_comp contDiffOn_const)
      ((c.smooth_coframe.mono (fun _ hz => hz.1.2)).clm_comp contDiffOn_const)
      (fun z hz => (c.invertible_coframe z hz.1.2).comp ⟨N, rfl⟩)
  refine ⟨U, g, f, hz₀, hgU, hf, ?_, (fun _ hz => hz.1.2), (fun _ hz => hz.2), ?_⟩
  · change ee (E z₀) = ee (endBandCoordinates p)
    rw [hE₀]
  intro t v hv hvU
  let z := (t.val, ei v)
  have hzS : z ∈ S := hvU.1.1
  have hRz : R z = (t.val, v) := by
    dsimp only [R, z]
    rw [ei.left_inv hv]
  obtain ⟨q, hqA, hmatch⟩ := hreverse t v (hRz ▸ hzS.1.2)
  have hKz : K z = q.val := by
    dsimp only [K]
    rw [hRz, hqA]
  have hQz : Q z = q := Subtype.ext ((hQval z hzS.1).trans hKz)
  have hEz : E z = endBandCoordinates q := by
    dsimp only [E]
    rw [hKz]
    rfl
  have hq : endBandCoordinates q ∈ ee.source := hEz ▸ hzS.2
  refine ⟨q, hq, ?_, hmatch.symm, ?_⟩
  · change ee (endBandCoordinates q) = ee (E z)
    rw [hEz]
  let F : Model (k + 1) → Band δ (IntrinsicBoundary.Point k M) := fun y => Q (t.val, y)
  have hF : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ F z.2 :=
    (hQ z hzS.1).comp z.2 (contMDiffAt_const.prodMk_space contMDiffAt_id)
  have hnear : ∀ᶠ v' in 𝓝 v, (t.val, ei v') ∈ U ∧ v' ∈ ei.source := by
    have he := ei.continuousOn.continuousAt (ei.open_source.mem_nhds hv)
    have hc : ContinuousAt (fun v' : IntrinsicInterior.Point k M => (t.val, ei v')) v :=
      continuousAt_const.prodMk he
    have hn : ∀ᶠ v' in 𝓝 v, (t.val, ei v') ∈ U :=
      hc.preimage_mem_nhds (U.isOpen.mem_nhds hvU)
    exact hn.and (ei.open_source.mem_nhds hv)
  have heq : ∀ᶠ v' in 𝓝 v,
      cylinder (fun r : Half δ (IntrinsicBoundary.Point k M) => C t r.val) (F (ei v')) =
      interiorIn (fun r : Half δ (IntrinsicBoundary.Point k M) => C t r.val) v' := by
    filter_upwards [hnear] with v' hv'
    have hR' : R (t.val, ei v') = (t.val, v') := by
      dsimp only [R]
      rw [ei.left_inv hv'.2]
    obtain ⟨q', hq'A, hq'match⟩ := hreverse t v' (hR' ▸ hv'.1.1.1.1.2)
    have hQ' : Q (t.val, ei v') = q' := by
      apply Subtype.ext
      rw [hQval _ hv'.1.1.1.1]
      dsimp only [K]
      rw [hR', hq'A]
    apply sliceIn_injective (fun t p => C t p.val) t
    rw [sliceIn_cylinder]
    change _ = sliceIn (fun t p => C t p.val) t
      (original (fun r : Half δ (IntrinsicBoundary.Point k M) => C t r.val) v'.val)
    rw [sliceIn_original]
    change totalCylinder (fun t p => C t p.val) (t, Q (t.val, ei v')) = _
    rw [hQ']
    exact hq'match
  have hcoord : ∀ y ∈ S₀, g y = ee (endBandCoordinates (Q y)) := by
    intro y hy
    change ee ((K y).2, -(K y).1) = ee ((Q y).val.2, -(Q y).val.1)
    rw [hQval y hy]
  have hspatial : (fun y => g (t.val, y)) =ᶠ[𝓝 z.2] ee ∘ endBandCoordinates ∘ F := by
    have hn := (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hS₀.mem_nhds hzS.1)
    filter_upwards [hn] with y hy
    exact hcoord (t.val, y) hy
  have hdg : mixedSpatialDerivative g z = fderiv ℝ (ee ∘ endBandCoordinates ∘ F) z.2 :=
    (mixedSpatialDerivative_eq
      ((hgU.contDiffAt (U.isOpen.mem_nhds hvU)).differentiableAt (by simp))).trans
        hspatial.fderiv_eq
  have hscalar := originalReverseMixedCanonical_squaredTransition_of_germ
    hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t) N c.anchor d.anchor v q F
    hF hQz hv hq heq (c.coframe z) (d.coframe (z.1, g z))
  dsimp only [f]
  rw [hdg]
  have hgz : ee (endBandCoordinates q) = g z := by
    change ee (endBandCoordinates q) = ee (E z)
    rw [hEz]
  dsimp only [z, ei, ee] at hgz
  simpa only [OriginalInteriorCanonicalChart.nativeCoframe,
    OriginalEndCanonicalChart.nativeCoframe, z, ei, ee, hgz] using hscalar.symm

end FsFltz.Geometry.IntrinsicCompletionGluing
