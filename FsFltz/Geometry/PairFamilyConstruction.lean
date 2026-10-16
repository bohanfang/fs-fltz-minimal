import FsFltz.Geometry.FamilyCompletionAssembly

/-!
# Constructing smooth witnessed pair families

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160; `def:chain`,
lines 163–169; and `sec:lean`, lines 788–814. The fixed compact domains,
Liouville primitives, ribbon embeddings and positive witnesses are the
input geometric data. Both localized completions and their compatible
presentations are constructed from the primitive families. The supplied
witness and ribbon maps are retained under the native inclusions.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold
set_option backward.isDefEq.respectTransparency false

namespace SmoothManifold

/-- Composition preserves both the topology and the actual immersion
condition of the native smooth embedding API. -/
def SmoothEmbedding.comp {a b c : ℕ} {M : SmoothManifold a}
    {N : SmoothManifold b} {P : SmoothManifold c}
    (g : N.SmoothEmbedding P) (f : M.SmoothEmbedding N) : M.SmoothEmbedding P where
  map := ⟨g.map ∘ f.map, g.map.contMDiff.comp f.map.contMDiff⟩
  embedding := g.embedding.comp f.embedding
  immersion := by
    intro x
    change Function.Injective (mfderiv 𝓘(ℝ, Model a) 𝓘(ℝ, Model c) (g.map ∘ f.map) x)
    rw [mfderiv_comp x (g.map.contMDiff.mdifferentiableAt (by simp))
      (f.map.contMDiff.mdifferentiableAt (by simp))]
    exact (g.immersion (f.map x)).comp (f.immersion x)

/-- Joint scalar regularity includes native smoothness of every interval
slice, without a separate pointwise smoothness assumption. -/
theorem IsSmoothIntervalScalarFamily.contMDiff_slice {d : ℕ} {M : SmoothManifold d}
    {b : Parameter → M.Point → ℝ} (hb : M.IsSmoothIntervalScalarFamily b)
    (t : Parameter) : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ (b t) := by
  obtain ⟨b', hs, he⟩ := hb
  rw [← he t]
  intro x
  let c := chartAt (Model d) x
  obtain ⟨U, hU, hsub, hf⟩ := hs x
  have hx := mem_chart_source (Model d) x
  have hy := c.map_source hx
  have hcoeff := hf.contDiffAt (hU.mem_nhds
    (hsub (show (t.val, c x) ∈ parameterInterval ×ˢ c.target from ⟨t.property, hy⟩)))
  have hc := (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (n := ∞) (x := x)).contMDiffAt
    (c.open_source.mem_nhds hx)
  apply (hcoeff.contMDiffAt.comp x (contMDiffAt_const.prodMk_space hc)).congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hx] with y hy
  change b' t.val y = b' t.val (c.symm (c y))
  rw [c.left_inv hy]

/-- Precomposing an interval map family by a globally jointly smooth family
preserves the genuine open parameter-endpoint extensions. -/
theorem isSmoothIntervalMapFamily_comp_of_contMDiff_family
    {d e f : ℕ} (M : SmoothManifold d) (N : SmoothManifold e) (P : SmoothManifold f)
    (g : Parameter → N.Point → P.Point) (hg : N.IsSmoothIntervalMapFamily P g)
    (k : ℝ → M.Point → N.Point)
    (hk : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
      (fun p : ℝ × M.Point => k p.1 p.2)) :
    M.IsSmoothIntervalMapFamily P (fun t x => g t (k t.val x)) := by
  obtain ⟨g', ⟨U, hU, hcover, hs⟩, he⟩ := hg
  let q : ℝ × M.Point → ℝ × N.Point := fun p => (p.1, k p.1 p.2)
  have hq : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model e)) ∞ q := contMDiff_fst.prodMk hk
  refine ⟨fun t x => g' t (k t x), ⟨q ⁻¹' U,
    hU.preimage hq.continuous, ?_, hs.comp hq.contMDiffOn (fun _ hp => hp)⟩, ?_⟩
  · intro p hp
    exact hcover ⟨hp.1, mem_univ _⟩
  · intro t
    funext x
    exact congrFun (he t) (k t.val x)

end SmoothManifold

namespace LiouvilleDomain.FlowCollar

/-- The two original open inclusions have identity model tangent map, so
pulling back any original form is literal restriction. -/
theorem pullback_originalInclusion {d k : ℕ} {D : LiouvilleDomain d}
    (C : FlowCollar D) (η : D.domain.extension.Form k)
    (z : C.localizedDomain.domain.extension.Point) :
    C.localizedDomain.domain.extension.pullback D.domain.extension C.originalInclusion.map η z =
      η z.val.val := by
  unfold SmoothManifold.pullback
  change (η z.val.val).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
      (fun y : C.localizedDomain.domain.extension.Point => y.val.val) z) = _
  erw [D.neighborhoodDomain.extension.mfderiv_comp_restrict_val D.domain.extension
    C.neighborhood z
    ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp)),
    D.domain.extension.mfderiv_restrict_val]
  ext vs
  rfl

end LiouvilleDomain.FlowCollar

/-- Assemble the actual witnessed pair on the extensions localized by two
constructed flow collars. Its ribbon map is the original embedding composed
with the native ribbon inclusion, and its positive witness is unchanged. -/
def localizedWitnessedPair {n : ℕ}
    (D : LiouvilleDomain (2 * n)) (F : LiouvilleDomain (2 * n - 2))
    (A : LiouvilleDomain.FlowCollar D) (B : LiouvilleDomain.FlowCollar F)
    (j : F.domain.extension.SmoothEmbedding D.domain.boundary)
    (b : D.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ b)
    (hpositive : ∀ x, 0 < b x)
    (hribbon : ∀ x ∈ F.domain.carrier,
      F.domain.extension.pullback D.domain.boundary j.map
        (fun y => b y • D.domain.boundaryForm D.liouville.primitive y) x =
        F.liouville.primitive x) : WitnessedPair n where
  ambientDomain := A.localizedDomain
  ribbonDomain := B.localizedDomain
  ribbonEmbedding := j.comp B.originalInclusion
  witness := b
  smooth_witness := hb
  positive_witness := hpositive
  ribbon_primitive := by
    intro x hx
    change B.localizedDomain.domain.extension.pullback D.domain.boundary
      (j.map ∘ B.originalInclusion.map)
      (fun y => b y • A.localizedDomain.domain.boundaryForm A.localizedDomain.liouville.primitive y) x =
      B.localizedDomain.liouville.primitive x
    rw [A.localized_boundaryForm]
    rw [B.localizedDomain.domain.extension.pullback_comp F.domain.extension D.domain.boundary
      (B.originalInclusion.map.contMDiff.mdifferentiable (by simp))
      (j.map.contMDiff.mdifferentiable (by simp))]
    rw [B.pullback_originalInclusion, B.original_primitive]
    exact hribbon x.val.val hx
  ambientCompletion := A.cylindricalCompletion
  ribbonCompletion := B.cylindricalCompletion

namespace CompactDomain

/-- The native ribbon embeddings remain jointly smooth after transport by
localized presentations, using the exact projection to the jointly smooth
original compact presentation. -/
theorem isSmoothIntervalRibbonEmbeddingFamily_of_localizedPresentations {n : ℕ}
    (D : CompactDomain (2 * n)) (F : CompactDomain (2 * n - 2))
    (L : Parameter → LiouvilleStructure D) (M : Parameter → LiouvilleStructure F)
    (j : Parameter → F.extension.SmoothEmbedding D.boundary)
    (hj : F.extension.IsSmoothIntervalMapFamily D.boundary (fun t => (j t).map))
    (A : (t : Parameter) → LiouvilleDomain.FlowCollar (⟨D, L t⟩ : LiouvilleDomain (2 * n)))
    (B : (t : Parameter) → LiouvilleDomain.FlowCollar (⟨F, M t⟩ : LiouvilleDomain (2 * n - 2)))
    (Ha : (t : Parameter) → DomainPresentationEquiv
      (A parameterZero).localizedDomain.domain (A t).localizedDomain.domain)
    (Hf : (t : Parameter) → DomainPresentationEquiv
      (B parameterZero).localizedDomain.domain (B t).localizedDomain.domain)
    (hHaboundary : ∀ t, (Ha t).boundaryEquiv =
      ((Diffeomorph.refl _ _ ∞) : D.boundary.SmoothEquiv D.boundary))
    (hf : ℝ → DomainPresentationEquiv F F)
    (hfs : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
      𝓘(ℝ, Model (2 * n - 2)) ∞
      (fun p : ℝ × F.extension.Point => (hf p.1).extensionEquiv p.2))
    (hHfprojection : ∀ t z, ((Hf t).extensionEquiv z).val.val =
      (hf t.val).extensionEquiv z.val.val) :
    (B parameterZero).localizedDomain.domain.extension.IsSmoothIntervalMapFamily
      D.boundary (fun t x => (Ha t).boundaryEquiv.invFun
        ((j t).map ((B t).originalInclusion.map ((Hf t).extensionEquiv x)))) := by
  have hpre : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n - 2)))
      𝓘(ℝ, Model (2 * n - 2)) ∞
      (fun p : ℝ × (B parameterZero).localizedDomain.domain.extension.Point =>
        (hf p.1).extensionEquiv ((B parameterZero).originalInclusion.map p.2)) :=
    hfs.comp (contMDiff_fst.prodMk
      ((B parameterZero).originalInclusion.map.contMDiff.comp contMDiff_snd))
  have hs := SmoothManifold.isSmoothIntervalMapFamily_comp_of_contMDiff_family
      (B parameterZero).localizedDomain.domain.extension F.extension D.boundary
      (fun t => (j t).map) hj
      (fun t x => (hf t).extensionEquiv ((B parameterZero).originalInclusion.map x)) hpre
  have he : (fun (t : Parameter) x => (Ha t).boundaryEquiv.invFun
      ((j t).map ((B t).originalInclusion.map ((Hf t).extensionEquiv x)))) =
      (fun (t : Parameter) x => (j t).map
        ((hf t.val).extensionEquiv ((B parameterZero).originalInclusion.map x))) := by
    funext t x
    rw [hHaboundary]
    change (j t).map (((Hf t).extensionEquiv x).val.val) = _
    rw [hHfprojection]
    rfl
  rw [he]
  exact hs

/-- Assemble the pair deformation from its actual constructed localized completion families. -/
def localizedPairDeformation {n : ℕ}
    (D : CompactDomain (2 * n)) (F : CompactDomain (2 * n - 2))
    (L : Parameter → LiouvilleStructure D) (M : Parameter → LiouvilleStructure F)
    (j : Parameter → F.extension.SmoothEmbedding D.boundary)
    (b : Parameter → D.boundary.Point → ℝ)
    (_hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (_hM : F.extension.IsSmoothIntervalFormFamily (fun t => (M t).primitive))
    (hj : F.extension.IsSmoothIntervalMapFamily D.boundary (fun t => (j t).map))
    (hb : D.boundary.IsSmoothIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x)
    (ambient : LocalizedCompletionFamily D L)
    (ribbon : LocalizedCompletionFamily F M)
    (hribbon : ∀ t x, x ∈ F.carrier →
      F.extension.pullback D.boundary (j t).map
        (fun y => b t y • D.boundaryForm (L t).primitive y) x = (M t).primitive x) : PairDeformation n := by
  let A := ambient.collars
  let B := ribbon.collars
  let Ha := ambient.compactPresentation
  let Hf := ribbon.compactPresentation
  let hf := ribbon.originalPresentation
  let pair := fun t => localizedWitnessedPair ⟨D, L t⟩ ⟨F, M t⟩ (A t) (B t)
    (j t) (b t) (hb.contMDiff_slice t) (hpositive t) (hribbon t)
  have hembedding := D.isSmoothIntervalRibbonEmbeddingFamily_of_localizedPresentations
    F L M j hj A B Ha Hf ambient.boundary_compactPresentation hf
    ribbon.smooth_originalPresentation ribbon.original_projection
  have hwitness : D.boundary.IsSmoothIntervalScalarFamily
      (fun t x => (pair t).witness ((Ha t).boundaryEquiv x)) := by
    obtain ⟨b', hs, he⟩ := hb
    refine ⟨b', hs, ?_⟩
    intro t
    funext x
    rw [he t]
    change b t x = b t ((Ha t).boundaryEquiv x)
    rw [ambient.boundary_compactPresentation]
    rfl
  let Q : PairDeformation n :=
    { pair := pair
      ambientPresentation := Ha
      ribbonPresentation := Hf
      ambientCompletionPresentation := ambient.completionPresentation
      ribbonCompletionPresentation := ribbon.completionPresentation
      ambientPrimitive_smooth := ambient.compactPrimitive_smooth
      ribbonPrimitive_smooth := ribbon.compactPrimitive_smooth
      ambientField_smooth := ambient.compactField_smooth
      ribbonField_smooth := ribbon.compactField_smooth
      ribbonEmbedding_smooth := hembedding
      witness_smooth := hwitness
      completedAmbientPrimitive_smooth := ambient.completedPrimitive_smooth
      completedRibbonPrimitive_smooth := ribbon.completedPrimitive_smooth
      completedAmbientField_smooth := ambient.completedField_smooth
      completedRibbonField_smooth := ribbon.completedField_smooth }
  exact Q

/-- Retain the actual compact and completion presentations of the same assembled pair family. -/
theorem exists_localized_pairDeformation_with_presentations {n : ℕ}
    (D : CompactDomain (2 * n)) (F : CompactDomain (2 * n - 2))
    (L : Parameter → LiouvilleStructure D) (M : Parameter → LiouvilleStructure F)
    (j : Parameter → F.extension.SmoothEmbedding D.boundary)
    (b : Parameter → D.boundary.Point → ℝ)
    (hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (hM : F.extension.IsSmoothIntervalFormFamily (fun t => (M t).primitive))
    (hj : F.extension.IsSmoothIntervalMapFamily D.boundary (fun t => (j t).map))
    (hb : D.boundary.IsSmoothIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x)
    (hribbon : ∀ t x, x ∈ F.carrier →
      F.extension.pullback D.boundary (j t).map
        (fun y => b t y • D.boundaryForm (L t).primitive y) x = (M t).primitive x) :
    ∃ (ambient : LocalizedCompletionFamily D L) (ribbon : LocalizedCompletionFamily F M)
      (Q : PairDeformation n),
      Q = D.localizedPairDeformation F L M j b hL hM hj hb hpositive ambient ribbon hribbon := by
  exact ⟨D.localizedCompletionFamily L hL, F.localizedCompletionFamily M hM, _, rfl⟩

/-- Fixed compact domain and ribbon data with jointly smooth Liouville
primitives, embeddings and positive witnesses construct a smooth deformation
of actual witnessed pairs, including both completed families. Both families
of collars and completions are produced here. The concrete pair formula
records the original embedding, witness and primitive restrictions. -/
theorem exists_localized_pairDeformation {n : ℕ}
    (D : CompactDomain (2 * n)) (F : CompactDomain (2 * n - 2))
    (L : Parameter → LiouvilleStructure D) (M : Parameter → LiouvilleStructure F)
    (j : Parameter → F.extension.SmoothEmbedding D.boundary)
    (b : Parameter → D.boundary.Point → ℝ)
    (hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (hM : F.extension.IsSmoothIntervalFormFamily (fun t => (M t).primitive))
    (hj : F.extension.IsSmoothIntervalMapFamily D.boundary (fun t => (j t).map))
    (hb : D.boundary.IsSmoothIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x)
    (hribbon : ∀ t x, x ∈ F.carrier →
      F.extension.pullback D.boundary (j t).map
        (fun y => b t y • D.boundaryForm (L t).primitive y) x = (M t).primitive x) :
    ∃ A : (t : Parameter) → LiouvilleDomain.FlowCollar (⟨D, L t⟩ : LiouvilleDomain (2 * n)),
      ∃ B : (t : Parameter) → LiouvilleDomain.FlowCollar (⟨F, M t⟩ : LiouvilleDomain (2 * n - 2)),
        ∃ Q : PairDeformation n,
          Q.pair = fun t => localizedWitnessedPair ⟨D, L t⟩ ⟨F, M t⟩ (A t) (B t)
            (j t) (b t) (hb.contMDiff_slice t) (hpositive t) (hribbon t) := by
  obtain ⟨ambient, ribbon, Q, rfl⟩ := D.exists_localized_pairDeformation_with_presentations
    F L M j b hL hM hj hb hpositive hribbon
  exact ⟨ambient.collars, ribbon.collars,
    D.localizedPairDeformation F L M j b hL hM hj hb hpositive ambient ribbon hribbon, rfl⟩

end CompactDomain

end FsFltz.Geometry
