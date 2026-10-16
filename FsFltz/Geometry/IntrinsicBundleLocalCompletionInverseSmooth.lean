import FsFltz.Geometry.IntrinsicBundleLocalCompletionInverse

/-!
# Smooth equivalences from original local completions

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199, and
`sec:lean`, lines 788–814. Actual real forward and spatial inverse patch
germs restrict to jointly smooth maps in the retained relative-open
family atlas. The resulting diffeomorphism uses the same strict slices.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle Topology
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicCompletionGluing

/-- Actual real chart germs restrict to a smooth map on the original open subspace. -/
theorem HasRealOpenMapGermsOn.contMDiff {E H X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] [TopologicalSpace X]
    (I : ModelWithCorners ℝ E H) [ChartedSpace H X] [IsManifold I ∞ X]
    {d : ℕ} (N : SmoothManifold d) (A : TopologicalSpace.Opens X) (f : A → N.Point)
    (hf : HasRealOpenMapGermsOn I N (A : Set X) f) : ContMDiff I 𝓘(ℝ, Model d) ∞ f := by
  intro x
  obtain ⟨e, he, hxe, U, hpU, β, hβ, heq⟩ := hf x.val x.property
  have hc := e.contMDiffOn_extend (I := I) (n := ∞) (IsManifold.subset_maximalAtlas (n := ∞) he)
  let W : TopologicalSpace.Opens X :=
    ⟨e.source ∩ e.extend I ⁻¹' U,
      hc.continuousOn.isOpen_inter_preimage e.open_source U.isOpen⟩
  let O : TopologicalSpace.Opens A := ⟨Subtype.val ⁻¹' W, W.isOpen.preimage continuous_subtype_val⟩
  let q : O → U := fun z => ⟨e.extend I z.val.val, z.property.2⟩
  have hq : ContMDiff I 𝓘(ℝ, E) ∞ q := by
    apply (ContMDiff.subtypeVal_comp_iff U q).mp
    intro z
    change ContMDiffAt I 𝓘(ℝ, E) ∞ (fun z : O => e.extend I z.val.val) z
    have hv : ContMDiff I I ∞ (fun z : O => z.val.val) :=
      contMDiff_subtype_val.comp contMDiff_subtype_val
    exact (e.contMDiffAt_extend (I := I) (n := ∞)
      (IsManifold.subset_maximalAtlas (n := ∞) he) z.property.1).comp z
      hv.contMDiffAt
  have hsame : β ∘ q = fun z : O => f z.val := by
    funext z
    exact heq z.val.val z.val.property z.property.1 z.property.2
  have hsmooth : ContMDiff I 𝓘(ℝ, Model d) ∞ (fun z : O => f z.val) :=
    hsame ▸ hβ.comp hq
  exact (contMDiffAt_subtype_iff (f := f) (x := (⟨x, hxe, hpU⟩ : O))).mp hsmooth.contMDiffAt

end FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle.LocalCompletionFamily

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {c : OriginalCompactChart (k := k) (M := M) (E := E)} {t : Parameter}

variable (F : LocalCompletionFamily P c t) (L : OriginalBundleLiouvilleLaws P)
  (g : Trivialization M (π M E)) (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g)
  (hbase : g.baseSet = univ) (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
  (eAs : ∀ s, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
    (Q.pair s).ambientDomain.domain.Point ∞)
  (hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs s y).val) x) =
      P.formInTrivialization g s x)
  (hc : ∀ s, HasNativeCoordinateExtensions (k := k)
    (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val))

/-- The same reference product, restricted to the original relative-open base. -/
abbrev referenceTarget : TopologicalSpace.Opens
    (Parameter × Q.source.ambientCompletion.ambient.manifold.Point) :=
  ⟨F.base ×ˢ univ, F.base_open.prod isOpen_univ⟩

/-- Changing only between the two literal subtype presentations of the base product. -/
def ambientReferenceOpenEquiv : F.localSource ≃ F.referenceTarget Q where
  toFun z := ⟨(parameter F.native.patches z.val,
    F.ambientReferenceTotalMap L g hg hbase Q hdim eAs hp hc z), z.property, mem_univ _⟩
  invFun z := F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc
    (⟨z.val.1, z.property.1⟩, z.val.2)
  left_inv z := F.ambientReferenceTotalInverse_map L g hg hbase Q hdim eAs hp hc z
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact F.ambientReferenceTotalInverse_parameter L g hg hbase Q hdim eAs hp hc _ _
    · exact F.ambientReferenceTotalMap_inverse L g hg hbase Q hdim eAs hp hc _ _

/-- Real inverse patch germs give native smoothness of this exact open inverse. -/
theorem smooth_ambientReferenceOpenEquiv_inverse_of_realGerms
    (hi : HasRealOpenPatchInverseGerms F.native.patches
      Q.source.ambientCompletion.ambient.manifold F.base
      (fun z => (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc z).val)) :
    letI := F.native.totalCharts
    ContMDiff (familyModel (2 * n)) (familyModel (k + 1)) ∞
      (F.ambientReferenceOpenEquiv L g hg hbase Q hdim eAs hp hc).symm := by
  let := F.native.totalCharts
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) F.native.width
  let A := F.referenceTarget Q
  let f : A → F.native.total := fun z =>
    (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc
      (⟨z.val.1, z.property.1⟩, z.val.2)).val
  apply (ContMDiff.subtypeVal_comp_iff F.localSource
    (F.ambientReferenceOpenEquiv L g hg hbase Q hdim eAs hp hc).symm).mp
  change ContMDiff (familyModel (2 * n)) (familyModel (k + 1)) ∞ f
  intro x
  let s : F.base := ⟨x.val.1, x.property.1⟩
  let q : A → ℝ × Q.source.ambientCompletion.ambient.manifold.Point :=
    fun z => (z.val.1.val, z.val.2)
  have hq : ContMDiff (familyModel (2 * n))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞ q :=
    (contMDiff_subtypeVal_Icc.prodMap contMDiff_id).comp contMDiff_subtype_val
  rcases hi s x.val.2 with ⟨U, hpU, γ, hγ, heq⟩ | ⟨U, hpU, γ, hγ, hr, heq⟩
  · let O : TopologicalSpace.Opens A := ⟨q ⁻¹' U, U.isOpen.preimage hq.continuous⟩
    let qO : O → U := fun z => ⟨q z.val, z.property⟩
    have hqO : ContMDiff (familyModel (2 * n))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞ qO :=
      (ContMDiff.subtypeVal_comp_iff U qO).mp (hq.comp contMDiff_subtype_val)
    let G : O → F.native.total := fun z =>
      totalInterior F.native.patches (z.val.val.1, γ (qO z))
    have hG : ContMDiff (familyModel (2 * n)) (familyModel (k + 1)) ∞ G :=
      F.native.smooth_totalInterior.comp
        ((contMDiff_fst.comp (contMDiff_subtype_val.comp contMDiff_subtype_val)).prodMk
          (hγ.comp hqO))
    have hs : ContMDiff (familyModel (2 * n)) (familyModel (k + 1)) ∞ (fun z : O => f z.val) := by
      convert hG using 1
      funext z
      exact heq ⟨z.val.val.1, z.val.property.1⟩ z.val.val.2 z.property
    exact (contMDiffAt_subtype_iff (f := f) (x := (⟨x, hpU⟩ : O))).mp hs.contMDiffAt
  · let O : TopologicalSpace.Opens A := ⟨q ⁻¹' U, U.isOpen.preimage hq.continuous⟩
    let qO : O → U := fun z => ⟨q z.val, z.property⟩
    have hqO : ContMDiff (familyModel (2 * n))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞ qO :=
      (ContMDiff.subtypeVal_comp_iff U qO).mp (hq.comp contMDiff_subtype_val)
    let b : U → Band F.native.width (IntrinsicBoundary.Point k M) :=
      fun z => ⟨(-(γ z).2, (γ z).1), hr z, mem_univ _⟩
    have hb : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
        𝓘(ℝ, Model (k + 1)) ∞ b := by
      intro z
      apply contMDiffAt_band_iff_val.mpr
      exact ((contMDiff_snd.comp hγ).neg.prodMk (contMDiff_fst.comp hγ)).contMDiffAt
    let G : O → F.native.total := fun z =>
      totalCylinder F.native.patches (z.val.val.1, b (qO z))
    have hG : ContMDiff (familyModel (2 * n)) (familyModel (k + 1)) ∞ G :=
      F.native.smooth_totalCylinder.comp
        ((contMDiff_fst.comp (contMDiff_subtype_val.comp contMDiff_subtype_val)).prodMk
          (hb.comp hqO))
    have hs : ContMDiff (familyModel (2 * n)) (familyModel (k + 1)) ∞ (fun z : O => f z.val) := by
      convert hG using 1
      funext z
      obtain ⟨p, hp, hfp⟩ := heq ⟨z.val.val.1, z.val.property.1⟩ z.val.val.2 z.property
      exact hfp.trans (congrArg (fun p => totalCylinder F.native.patches (z.val.val.1, p))
        (Subtype.ext hp))
    exact (contMDiffAt_subtype_iff (f := f) (x := (⟨x, hpU⟩ : O))).mp hs.contMDiffAt

omit [T2Space M] [SecondCountableTopology M] [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Actual forward real germs and the retained smooth parameter projection
give native joint smoothness of the exact open comparison. -/
theorem smooth_ambientReferenceOpenEquiv_of_realGerms
    (hf : letI := F.native.totalCharts
      HasRealOpenMapGermsOn (familyModel (k + 1))
        Q.source.ambientCompletion.ambient.manifold (F.localSource : Set F.native.total)
        (F.ambientReferenceTotalMap L g hg hbase Q hdim eAs hp hc)) :
    letI := F.native.totalCharts
    ContMDiff (familyModel (k + 1)) (familyModel (2 * n)) ∞
      (F.ambientReferenceOpenEquiv L g hg hbase Q hdim eAs hp hc) := by
  let := F.native.totalCharts
  let := F.native.total_isManifold
  have hm : ContMDiff (familyModel (k + 1)) 𝓘(ℝ, Model (2 * n)) ∞
      (F.ambientReferenceTotalMap L g hg hbase Q hdim eAs hp hc) :=
    hf.contMDiff (familyModel (k + 1)) Q.source.ambientCompletion.ambient.manifold
      F.localSource _
  apply (ContMDiff.subtypeVal_comp_iff (F.referenceTarget Q)
    (F.ambientReferenceOpenEquiv L g hg hbase Q hdim eAs hp hc)).mp
  exact (F.native.smooth_parameter.comp contMDiff_subtype_val).prodMk hm

/-- Both proved real germ conclusions assemble a diffeomorphism with the
literal original comparison and inverse. No further native family data
or independent smoothness premise is required by this consumer. -/
def ambientReferenceTotalDiffeomorphOfRealGerms
    (hf : letI := F.native.totalCharts
      HasRealOpenMapGermsOn (familyModel (k + 1))
        Q.source.ambientCompletion.ambient.manifold (F.localSource : Set F.native.total)
        (F.ambientReferenceTotalMap L g hg hbase Q hdim eAs hp hc))
    (hi : HasRealOpenPatchInverseGerms F.native.patches
      Q.source.ambientCompletion.ambient.manifold F.base
      (fun z => (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc z).val)) :
    letI := F.native.totalCharts
    Diffeomorph (familyModel (k + 1)) (familyModel (2 * n))
      F.localSource (F.referenceTarget Q) ∞ := by
  let := F.native.totalCharts
  exact {
    toEquiv := F.ambientReferenceOpenEquiv L g hg hbase Q hdim eAs hp hc
    contMDiff_toFun := F.smooth_ambientReferenceOpenEquiv_of_realGerms L g hg hbase Q hdim eAs hp hc hf
    contMDiff_invFun := F.smooth_ambientReferenceOpenEquiv_inverse_of_realGerms L g hg hbase Q hdim eAs hp hc hi }

@[simp] theorem ambientReferenceTotalDiffeomorphOfRealGerms_toEquiv
    (hf : letI := F.native.totalCharts
      HasRealOpenMapGermsOn (familyModel (k + 1))
        Q.source.ambientCompletion.ambient.manifold (F.localSource : Set F.native.total)
        (F.ambientReferenceTotalMap L g hg hbase Q hdim eAs hp hc))
    (hi : HasRealOpenPatchInverseGerms F.native.patches
      Q.source.ambientCompletion.ambient.manifold F.base
      (fun z => (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc z).val)) :
    letI := F.native.totalCharts
    (F.ambientReferenceTotalDiffeomorphOfRealGerms L g hg hbase Q hdim eAs hp hc hf hi).toEquiv =
      F.ambientReferenceOpenEquiv L g hg hbase Q hdim eAs hp hc := rfl

/-- The original local-to-global comparison and its inverse are one actual
native diffeomorphism over precisely the retained local base. Both
smoothness proofs consume the constructed real germs, rather than supplied
completion-map regularity. -/
def ambientReferenceTotalDiffeomorph
    (eBs : ∀ u, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
      (Q.pair u).ambientDomain.domain.boundary)
    (hb : ∀ u b, (Q.pair u).ambientDomain.domain.boundaryInclusion.map (eBs u b) =
      (eAs u b.val).val)
    (hsquareB : ∀ u b, (Q.ambientPresentation u).boundaryEquiv (eBs parameterZero b) = eBs u b)
    (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
    (hsquareA : ∀ s x, (Q.ambientPresentation s).extensionEquiv
      (eAs parameterZero (R s.val x)).val = (eAs s x).val) :
    letI := F.native.totalCharts
    Diffeomorph (familyModel (k + 1)) (familyModel (2 * n))
      F.localSource (F.referenceTarget Q) ∞ := by
  let := F.native.totalCharts
  exact F.ambientReferenceTotalDiffeomorphOfRealGerms L g hg hbase Q hdim eAs hp hc
    (F.ambientReferenceTotalMap_realGerms L g hg hbase Q hdim eAs hp hc
      eBs hb hsquareB R hR hsquareA)
    (F.ambientReferenceTotalInverse_realGerms L g hg hbase Q hdim eAs hp hc
      eBs hb hsquareB R hR hsquareA)

/-- Forgetting regularity leaves exactly the already defined forward and inverse maps. -/
@[simp] theorem ambientReferenceTotalDiffeomorph_toEquiv
    (eBs : ∀ u, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
      (Q.pair u).ambientDomain.domain.boundary)
    (hb : ∀ u b, (Q.pair u).ambientDomain.domain.boundaryInclusion.map (eBs u b) =
      (eAs u b.val).val)
    (hsquareB : ∀ u b, (Q.ambientPresentation u).boundaryEquiv (eBs parameterZero b) = eBs u b)
    (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
    (hsquareA : ∀ s x, (Q.ambientPresentation s).extensionEquiv
      (eAs parameterZero (R s.val x)).val = (eAs s x).val) :
    letI := F.native.totalCharts
    (F.ambientReferenceTotalDiffeomorph L g hg hbase Q hdim eAs hp hc
      eBs hb hsquareB R hR hsquareA).toEquiv =
      F.ambientReferenceOpenEquiv L g hg hbase Q hdim eAs hp hc := rfl

end FsFltz.Geometry.IntrinsicSmoothBundle.LocalCompletionFamily
