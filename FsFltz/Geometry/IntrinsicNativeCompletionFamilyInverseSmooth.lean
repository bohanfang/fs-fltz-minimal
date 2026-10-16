import FsFltz.Geometry.IntrinsicNativeCompletionFamilyInverse
import FsFltz.Geometry.PrescribedFamilyCollarInverse

/-!
# Smooth inverse in the original native completion family

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and
`sec:lean`, lines 788–814. Real parameter-preserving inverse germs of the
actual cylinder comparison restrict to the parameter interval and take
values in the original full cylinder patch. They retain the original
attachment topology and family atlas, including the parameter endpoints.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t (b : IntrinsicBoundary.Point k M), C t (0, b) = b.val)
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hmix : HasRealMixedGerms (δ := δ) C)

local instance : ChartedSpace (Model (k + 1))
    (Band δ (IntrinsicBoundary.Point k M)) := bandChartedSpace δ

private def intoBand (p : Band δ (IntrinsicBoundary.Point k M))
    {X : Type*} (f : X → ℝ × IntrinsicBoundary.Point k M) (x : X) :
    Band δ (IntrinsicBoundary.Point k M) :=
  if hx : f x ∈ Band δ (IntrinsicBoundary.Point k M) then ⟨f x, hx⟩ else p

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
private theorem intoBand_val (p : Band δ (IntrinsicBoundary.Point k M))
    {X : Type*} (f : X → ℝ × IntrinsicBoundary.Point k M) (x : X)
    (hx : f x ∈ Band δ (IntrinsicBoundary.Point k M)) :
    (intoBand p f x).val = f x := by
  simp only [intoBand, hx, ↓reduceDIte]

include hboundary hmix in
/-- A real local inverse of the parameter-retaining cylinder map gives a
smooth inverse of the same bijection in the original family atlas. The
first coordinate is identified before restricting to `[0,1]`. -/
theorem contMDiffAt_inverse_of_real_cylinder
    (N : SmoothManifold d)
    (A : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) ≃
      Parameter × N.Point)
    (β : ℝ → IntrinsicBoundary.Point k M × ℝ → N.Point)
    (a : ℝ)
    (hsquare : ∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
      a < -p.val.1 →
      A (totalCylinder (fun t p => C t p.val) (t, p)) =
        (t, β t.val (p.val.2, -p.val.1)))
    (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ)
    (hr : a < r) (hrδ : -r < δ)
    (hl : IsLocalDiffeomorphAt
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (fun q : ℝ × (IntrinsicBoundary.Point k M × ℝ) => (q.1, β q.1 q.2))
      (t.val, (x, r))) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffAt (familyModel d) (familyModel (k + 1)) ∞ A.symm
      (t, β t.val (x, r)) := by
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let p : Band δ (IntrinsicBoundary.Point k M) := ⟨(-r, x), ⟨hrδ, mem_univ _⟩⟩
  let y : Parameter × N.Point := (t, β t.val (x, r))
  let v : Parameter × N.Point → ℝ × (IntrinsicBoundary.Point k M × ℝ) :=
    fun z => hl.localInverse (z.1.val, z.2)
  have hu : ContMDiff (familyModel d)
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (fun z : Parameter × N.Point => (z.1.val, z.2)) :=
    contMDiff_subtypeVal_Icc.prodMap contMDiff_id
  have hv : ContMDiffAt (familyModel d)
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ))) ∞ v y :=
    hl.localInverse_contMDiffAt.comp y
    hu.contMDiffAt
  have hvy : v y = (t.val, (x, r)) :=
    hl.localInverse_left_inv hl.localInverse_mem_target
  let f : Parameter × N.Point → ℝ × IntrinsicBoundary.Point k M :=
    fun z => (-(v z).2.2, (v z).2.1)
  have hf : ContMDiffAt (familyModel d)
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞ f y :=
    (contMDiffAt_snd.comp y (contMDiffAt_snd.comp y hv)).neg.prodMk
      (contMDiffAt_fst.comp y (contMDiffAt_snd.comp y hv))
  have hfy : f y = p.val := by dsimp [f, p]; rw [hvy]
  have hnBand : ∀ᶠ z in 𝓝 y, f z ∈ Band δ (IntrinsicBoundary.Point k M) :=
    hf.continuousAt.preimage_mem_nhds
      ((isOpen_Iio.prod isOpen_univ).mem_nhds (hfy.symm ▸ p.property))
  let g : Parameter × N.Point → Parameter × Band δ (IntrinsicBoundary.Point k M) :=
    fun z => (z.1, intoBand p f z)
  have hg : ContMDiffAt (familyModel d) (familyModel (k + 1)) ∞ g y := by
    apply contMDiffAt_fst.prodMk
    apply contMDiffAt_band_iff_val.mpr
    apply hf.congr_of_eventuallyEq
    filter_upwards [hnBand] with z hz
    exact intoBand_val p f z hz
  have hsmooth : ContMDiffAt (familyModel d) (familyModel (k + 1)) ∞
      (totalCylinder c ∘ g) y :=
    (contMDiff_totalCylinder hδ C hboundary hzero hjoint hmix _).comp y hg
  apply hsmooth.congr_of_eventuallyEq
  have hnInv : ∀ᶠ z in 𝓝 y,
      (fun q : ℝ × (IntrinsicBoundary.Point k M × ℝ) => (q.1, β q.1 q.2))
        (v z) = (z.1.val, z.2) :=
    (hu y).continuousAt.eventually hl.localInverse_eventuallyEq_right
  have hnRadius : ∀ᶠ z in 𝓝 y, a < (v z).2.2 :=
    (contMDiffAt_snd.comp y (contMDiffAt_snd.comp y hv)).continuousAt.preimage_mem_nhds
      (isOpen_Ioi.mem_nhds (show (v y).2.2 ∈ Ioi a by rw [hvy]; exact hr))
  filter_upwards [hnBand, hnInv, hnRadius] with z hz hzinv hzr
  apply A.injective
  rw [A.apply_symm_apply]
  have ht : (v z).1 = z.1.val := congrArg Prod.fst hzinv
  have hβz : β z.1.val (v z).2 = z.2 := by
    have h := congrArg Prod.snd hzinv
    change β (v z).1 (v z).2 = z.2 at h
    rwa [ht] at h
  change z = A (totalCylinder c (z.1, intoBand p f z))
  rw [hsquare z.1 (intoBand p f z) (by
    rw [intoBand_val p f z hz]; dsimp only [f]; simpa only [neg_neg] using hzr)]
  apply Prod.ext
  · rfl
  rw [intoBand_val p f z hz]
  dsimp only [f]
  simpa only [neg_neg] using hβz.symm

end FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.PairDeformation
open IntrinsicLiouville IntrinsicCompletionGluing

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
  (α : Parameter → Form k M 1)
  (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
    (Q.pair t).ambientDomain.domain.Point ∞)
  (hp : ∀ t x, ((Q.pair t).ambientDomain.liouville.primitive (e t x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (e t y).val) x) = α t x)
  (hc : ∀ t, HasNativeCoordinateExtensions (k := k)
    (Q.pair t).ambientDomain.domain.extension (fun x => (e t x).val))
  (b : ∀ t, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
    (Q.pair t).ambientDomain.domain.boundary)
  (hb : ∀ t x, (Q.pair t).ambientDomain.domain.boundaryInclusion.map (b t x) = (e t x.val).val)
  (hsquareB : ∀ t x, (Q.ambientPresentation t).boundaryEquiv (b parameterZero x) = b t x)
  (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
  (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
  (hsquareA : ∀ t x, (Q.ambientPresentation t).extensionEquiv
    (e parameterZero (R t.val x)).val = (e t x).val)
  {δ : ℝ} (hδ : 0 < δ) (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t x, C t (0, x) = x.val)
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hmix : HasRealMixedGerms (δ := δ) C)
  (hode : ∀ t x, IsMIntegralCurveOn (fun s => C t (s, x))
    (fun z => -liouvilleVector (α t) (exteriorDerivative (α t)) z) (Ico 0 δ))
  (q : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
    (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point)
  (hqnative : ∀ t x,
    q (original (totalCollar (fun t p => C t p.val)) (t, x)) = Q.ambientNativeReferenceMap e t x)
  (hqend : ∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
    q (totalCylinder (fun t p => C t p.val) (t, p)) =
      (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.val.2, -p.val.1))

include hdim α hp hc hb hsquareB hboundary hzero hjoint hmix hode in
/-- Smooth inverse germs at every point of the actual reference outward
end, including radius zero. The real family inverse function theorem
supplies the germ across the seam and both parameter endpoints. -/
theorem contMDiffAt_ambientNativeTotalEquiv_symm_end
    (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ) (hr : 0 ≤ r) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiffAt (familyModel (2 * n)) (familyModel (k + 1)) ∞
      (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm
      (t, (Q.pair parameterZero).ambientCompletion.endMap (b parameterZero x, r)) := by
  obtain ⟨a, ha, β, hβ, heβ, _, hβend⟩ :=
    Q.exists_ambientNativeCylinderFamily_extension hdim α e hp hc b hb hsquareB C hode hzero
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let B := (b parameterZero).prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  have hl₀ : IsLocalDiffeomorphAt
      ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model (2 * n)) ∞
      (fun p : IntrinsicBoundary.Point k M × ℝ =>
        (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.1, p.2))
      (x, r) :=
    (B.isLocalDiffeomorph (x, r)).comp 𝓘(ℝ, Model (2 * n))
      (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point
      ((Q.ambientCompletionPresentation t).isLocalDiffeomorph_prescribedEndMap (B (x, r)))
  have heq : (fun p : IntrinsicBoundary.Point k M × ℝ => β t.val p) =ᶠ[𝓝 (x, r)]
      (fun p : IntrinsicBoundary.Point k M × ℝ =>
        (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.1, p.2)) := by
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (isOpen_Ioi.mem_nhds (show r ∈ Ioi a from lt_of_lt_of_le ha hr))] with p hp'
    exact heβ t p.1 p.2 hp'
  have hbij : Function.Bijective (mfderiv
      ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model (2 * n))
      (fun p : IntrinsicBoundary.Point k M × ℝ => β t.val p) (x, r)) := by
    rw [heq.mfderiv_eq]
    exact (tangentSpaceCast 𝓘(ℝ, Model (2 * n))
      ((Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero x, r))
      (β t.val (x, r))).bijective.comp
        ((hl₀.mfderivToContinuousLinearEquiv (by simp)).bijective)
  have hl : IsLocalDiffeomorphAt
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (IntrinsicBoundary.Point k M × ℝ) => (p.1, β p.1 p.2))
      (t.val, (x, r)) := by
    have hM : IsManifold ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) ∞
        (IntrinsicBoundary.Point k M × ℝ) := inferInstance
    let : ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
      prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
    rw [← modelWithCornersSelf_prod] at hM hβ hbij ⊢
    exact isLocalDiffeomorphAt_parameterMap_of_bijective_slice
      (fun p : ℝ × (IntrinsicBoundary.Point k M × ℝ) => β p.1 p.2) hβ t.val (x, r) hbij
  have hsquare : ∀ (s : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
      a < -p.val.1 →
      Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend (totalCylinder c (s, p)) =
        (s, β s.val (p.val.2, -p.val.1)) := by
    intro s p hp'
    apply Prod.ext
    · rfl
    · exact (hqend s p).trans (heβ s p.val.2 (-p.val.1) hp').symm
  have h := contMDiffAt_inverse_of_real_cylinder hδ C hboundary hzero hjoint hmix
    (Q.pair parameterZero).ambientCompletion.ambient.manifold
    (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend)
    β a hsquare t x r (lt_of_lt_of_le ha hr) (by linarith) hl
  rwa [hβend t x r hr] at h

include hdim α hp hc hb hsquareB hR hboundary hzero hjoint hmix hode in
/-- The proved smooth native map and the actual parameter projection give
joint smoothness of the original parameter-preserving equivalence. -/
theorem contMDiff_ambientNativeTotalEquiv :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiff (familyModel (k + 1)) (familyModel (2 * n)) ∞
      (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend) := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  exact (contMDiff_parameter hδ C hboundary hzero hjoint hmix).prodMk
    (Q.contMDiff_ambientNativeTotalMap hdim α e hp hc b hb hsquareB R hR hsquareA
      hδ C hboundary hzero hjoint hmix hode q hqnative hqend)

include hdim α hp hc hb hsquareB hR hboundary hzero hjoint hmix hode in
/-- The inverse of the original comparison is jointly smooth everywhere
in the original family atlas. The actual compact interior and nonnegative
reference end cover the reference completion. -/
theorem contMDiff_ambientNativeTotalEquiv_symm :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    ContMDiff (familyModel (2 * n)) (familyModel (k + 1)) ∞
      (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  let K := (Q.pair parameterZero).ambientCompletion
  rintro ⟨t, y⟩
  by_cases hy : y ∈ K.inclusion.map '' interior (Q.pair parameterZero).ambientDomain.domain.carrier
  · obtain ⟨x, hx, rfl⟩ := hy
    exact Q.contMDiffAt_ambientNativeTotalEquiv_symm_compactInterior e b R hsquareA
      hδ C q hqnative hqend hdim hR hboundary hzero hjoint hmix t x hx
  · have hyend : y ∈ range (fun p : (Q.pair parameterZero).ambientDomain.domain.boundary.Point ×
        Ici (0 : ℝ) => K.endMap (p.1, p.2)) := by
      rw [K.range_nonnegative_endMap]
      exact hy
    obtain ⟨⟨x, ⟨r, hr⟩⟩, rfl⟩ := hyend
    have h := Q.contMDiffAt_ambientNativeTotalEquiv_symm_end hdim α e hp hc b hb hsquareB
      R hsquareA hδ C hboundary hzero hjoint hmix hode q hqnative hqend
      t ((b parameterZero).symm x) r hr
    simpa only [Diffeomorph.apply_symm_apply] using h

include hdim α hp hc hb hsquareB hR hboundary hzero hjoint hmix hode in
/-- The parameter-preserving comparison is an actual diffeomorphism from
the original completion-family atlas to the reference completed ambient
product. Its forward map and inverse are the same proved equivalence. -/
def ambientNativeTotalDiffeomorph :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    Diffeomorph (familyModel (k + 1)) (familyModel (2 * n))
      (TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val))
      (Parameter × (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point) ∞ := by
  let := totalFamilyChartedSpace hδ C hzero hjoint
  exact
    { toEquiv := Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend
      contMDiff_toFun := Q.contMDiff_ambientNativeTotalEquiv hdim α e hp hc b hb hsquareB
        R hR hsquareA hδ C hboundary hzero hjoint hmix hode q hqnative hqend
      contMDiff_invFun := Q.contMDiff_ambientNativeTotalEquiv_symm hdim α e hp hc b hb hsquareB
        R hR hsquareA hδ C hboundary hzero hjoint hmix hode q hqnative hqend }

include hdim α hp hc hb hsquareB hR hboundary hzero hjoint hmix hode in
/-- The diffeomorphism has the prescribed parameter and spatial map on
every point of the original quotient. -/
@[simp] theorem ambientNativeTotalDiffeomorph_apply
    (z : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)) :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    Q.ambientNativeTotalDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
      hδ C hboundary hzero hjoint hmix hode q hqnative hqend z =
        (parameter (fun t p => C t p.val) z, q z) := rfl

include hdim α hp hc hb hsquareB hR hboundary hzero hjoint hmix hode in
/-- Forgetting smoothness recovers the original equivalence exactly. -/
@[simp] theorem ambientNativeTotalDiffeomorph_toEquiv :
    letI := totalFamilyChartedSpace hδ C hzero hjoint
    (Q.ambientNativeTotalDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
      hδ C hboundary hzero hjoint hmix hode q hqnative hqend).toEquiv =
        Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend := rfl

end FsFltz.Geometry.PairDeformation
