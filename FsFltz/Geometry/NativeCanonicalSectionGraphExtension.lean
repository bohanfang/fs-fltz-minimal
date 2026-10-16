import FsFltz.Geometry.NativeCoordinateCanonicalSection
import FsFltz.Geometry.PrescribedMaslovSectionExtension

/-!
# Correcting native section graph extensions

Source: `geoemtric-part-fsf.tex`, smooth-extension convention, lines 119–122;
`def:maslov`, lines 212–232; and `sec:lean`, lines 794–814.
A smooth map into the native canonical-square total space may move its base
point away from the prescribed locus. Natural square multiplication is smooth
for such maps. A local coframe correction then constructs an actual section
over the source point, retaining every prescribed graph value and its full
tensor image. Neither scalar nor tensor regularity is supplied.

The input graph map is a real-open smooth extension. Its existence from bare
boundary-manifold `ContMDiff ∞`, and the vertical canonical-square atlas of an
arbitrary varying completed family, remain separate foundations. This module
does not assert either correspondence or the geometric target.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Bundle

namespace FsFltz.Geometry

section NativeBundleMap

variable {E H B D HD X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [TopologicalSpace HD] [TopologicalSpace X] [ChartedSpace HD X]
  {I : ModelWithCorners ℝ E H} {IX : ModelWithCorners ℝ D HD} {n : ℕ}
  {J : B → Model (2 * n) →L[ℝ] Model (2 * n)}

/-- Natural square multiplication is smooth on arbitrary native
bundle-valued maps, with no condition on their base projection. -/
theorem verticalCanonicalTensorSquareMap_smooth
    (hJ : ContMDiff I 𝓘(ℝ, Model (2 * n) →L[ℝ] Model (2 * n)) ∞ J)
    (hJsq : ∀ x v, J x (J x v) = -v)
    (F : X → TotalSpace ℂ (fun x : B => CanonicalTensorSquare (J x)))
    (hF : let a := verticalCanonicalTensorSquareVectorPrebundle hJ hJsq
      letI := a.totalSpaceTopology
      letI := a.toFiberBundle
      ContMDiff IX (I.prod 𝓘(ℝ, ℂ)) ∞ F) :
    ContMDiff IX 𝓘(ℝ, SquaredCanonicalTensor n) ∞
      (fun x => (canonicalSquareMap (J (F x).proj) (F x).snd).val) := by
  let a := verticalCanonicalTensorSquareVectorPrebundle hJ hJsq
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  intro x
  let c := verticalCanonicalChartAt hJ hJsq (F x).proj
  have hx : (F x).proj ∈ c.domain := mem_verticalCanonicalChartAt_domain hJ hJsq _
  obtain ⟨hb, hq⟩ := Bundle.contMDiffAt_totalSpace.mp (hF x)
  have hg := (c.smooth_squaredGenerator.contMDiffAt
    (c.isOpen_domain.mem_nhds hx)).comp x hb
  have hm : ContDiff ℝ ∞
      (fun p : ℂ × SquaredCanonicalTensor n => p.1 • p.2) :=
    contDiff_fst.smul contDiff_snd
  apply (hm.contDiffAt.comp_contMDiffAt (hq.prodMk_space hg)).congr_of_eventuallyEq
  filter_upwards [hb.continuousAt.preimage_mem_nhds (c.isOpen_domain.mem_nhds hx)] with z hz
  have hr := c.reconstruction hz (canonicalSquareMap (J (F z).proj) (F z).snd)
  rw [c.coefficient_squareMap] at hr
  exact hr

end NativeBundleMap

namespace NativeCoordinateCanonicalPatch

variable {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {P : Model (2 * n) ≃L[ℝ] F} {K : E → F →L[ℝ] F} {A : Set E}
  (c : NativeCoordinateCanonicalPatch P K A)

/-- Native smoothness of an arbitrary map into the constructed bundle.
Its base projection is not required to be the identity. -/
def IsSmoothBundleMap
    (G : c.domain → TotalSpace ℂ (fun z : c.domain => CanonicalTensorSquare (c.complex z))) : Prop :=
  let a := verticalCanonicalTensorSquareVectorPrebundle c.smooth_complex c.complex_sq
  letI := a.totalSpaceTopology
  letI := a.toFiberBundle
  ContMDiff 𝓘(ℝ, E) ((𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) ∞ G

open scoped Classical in
def bundleMapTensor
    (G : c.domain → TotalSpace ℂ (fun z : c.domain => CanonicalTensorSquare (c.complex z)))
    (z : E) : SquaredCanonicalTensor n :=
  if hz : z ∈ c.domain then
    (canonicalSquareMap (c.complex (G ⟨z, hz⟩).proj) (G ⟨z, hz⟩).snd).val
  else 0

theorem bundleMapTensor_apply
    (G : c.domain → TotalSpace ℂ (fun z : c.domain => CanonicalTensorSquare (c.complex z)))
    {z : E} (hz : z ∈ c.domain) :
    c.bundleMapTensor G z =
      (canonicalSquareMap (c.complex (G ⟨z, hz⟩).proj) (G ⟨z, hz⟩).snd).val := by
  simp only [bundleMapTensor, hz, ↓reduceDIte]

/-- Full tensor regularity is derived from native bundle-map smoothness,
even when the bundle map moves its base away from the original locus. -/
theorem smooth_bundleMapTensor
    (G : c.domain → TotalSpace ℂ (fun z : c.domain => CanonicalTensorSquare (c.complex z)))
    (hG : c.IsSmoothBundleMap G) : ContDiffOn ℝ ∞ (c.bundleMapTensor G) c.domain := by
  have hs := verticalCanonicalTensorSquareMap_smooth c.smooth_complex c.complex_sq G hG
  intro z hz
  have he : (fun w : c.domain => c.bundleMapTensor G w.val) =
      (fun w : c.domain => (canonicalSquareMap (c.complex (G w).proj) (G w).snd).val) :=
    funext (fun w => c.bundleMapTensor_apply G w.property)
  rw [← he] at hs
  exact ((contMDiffAt_subtype_iff.mp (hs ⟨z, hz⟩)).contDiffAt).contDiffWithinAt

/-- A smooth native bundle-valued extension of a graph is rectified into
an actual smooth nonzero section. Projection is prescribed only on `A`.
Every original tensor value on `A` is preserved literally. -/
theorem exists_nonzeroSection_of_bundleMap
    {p : E} (hp : p ∈ c.domain) (hpA : p ∈ A)
    (G : c.domain → TotalSpace ℂ (fun z : c.domain => CanonicalTensorSquare (c.complex z)))
    (hG : c.IsSmoothBundleMap G)
    (hproj : ∀ z : c.domain, z.val ∈ A → (G z).proj = z)
    (hnz : (G ⟨p, hp⟩).snd ≠ 0) :
    ∃ V : TopologicalSpace.Opens E, ∃ hV : (V : Set E) ⊆ c.domain,
      ∃ _ : p ∈ V,
      ∃ σ : ∀ z : V, CanonicalTensorSquare ((c.restrict V hV).complex z),
        (c.restrict V hV).IsSmoothSection σ ∧
        (∀ z : V, σ z ≠ 0) ∧
        ∀ (z : V), z.val ∈ A →
          (canonicalSquareMap ((c.restrict V hV).complex z) (σ z)).val =
            (canonicalSquareMap (c.complex (G ⟨z.val, hV z.property⟩).proj)
              (G ⟨z.val, hV z.property⟩).snd).val := by
  let L := fun z : E => coframeComplexStructure (c.normalizedCoframe z)
  have hL : ContDiffOn ℝ ∞ L c.domain :=
    contDiffOn_coframeComplexStructure c.smooth_normalizedCoframe
      (fun z hz => c.invertible_normalizedCoframe hz)
  have hLsq : ∀ z ∈ c.domain, ∀ v, L z (L z v) = -v := by
    intro z hz v
    exact c.complex_sq ⟨z, hz⟩ v
  have hc : ∀ z ∈ (c.domain : Set E) ∩ A,
      IsSquaredCanonicalTensor (L z) (c.bundleMapTensor G z) := by
    intro z hz
    rw [c.bundleMapTensor_apply G hz.1]
    change IsSquaredCanonicalTensor (c.complex ⟨z, hz.1⟩) _
    have he := congrArg c.complex (hproj ⟨z, hz.1⟩ hz.2)
    rw [← he]
    exact (canonicalSquareMap _ (G ⟨z, hz.1⟩).snd).property
  have hn : c.bundleMapTensor G p ≠ 0 := by
    intro hzero
    apply hnz
    apply (canonicalSquareMap_bijective _ (c.complex_sq (G ⟨p, hp⟩).proj)).1
    apply Subtype.ext
    simpa only [map_zero, Submodule.coe_zero, c.bundleMapTensor_apply G hp] using hzero
  obtain ⟨V, hVc, hVo, hpV, q, hq, hqc, hqn, hqe⟩ :=
    exists_smooth_local_canonicalCorrection c.domain.isOpen hp hpA hL hLsq
      (c.smooth_bundleMapTensor G hG) hc hn
  let W : TopologicalSpace.Opens E := ⟨V, hVo⟩
  let d := c.restrict W hVc
  let σ : ∀ z : W, CanonicalTensorSquare (d.complex z) := fun z =>
    (canonicalSquareEquivOfComplexStructure _ (d.complex_sq z)).symm ⟨q z.val, hqc _ z.property⟩
  have hσ : ∀ z : W, (canonicalSquareMap (d.complex z) (σ z)).val = q z.val := by
    intro z
    exact congrArg Subtype.val ((canonicalSquareEquivOfComplexStructure _
      (d.complex_sq z)).apply_symm_apply _)
  refine ⟨W, hVc, hpV, σ, ?_, ?_, ?_⟩
  · apply (verticalCanonicalTensorSquareSection_smooth_iff d.smooth_complex d.complex_sq σ).mpr
    simp_rw [hσ]
    intro z
    exact contMDiffAt_subtype_iff.mpr
      (contMDiffAt_iff_contDiffAt.mpr (hq.contDiffAt (hVo.mem_nhds z.property)))
  · intro z hz
    have he := hσ z
    rw [hz, map_zero, Submodule.coe_zero] at he
    exact hqn _ z.property he.symm
  · intro z hzA
    rw [hσ, hqe z.val ⟨z.property, hzA⟩, c.bundleMapTensor_apply G (hVc z.property)]

end NativeCoordinateCanonicalPatch

namespace NativeCoordinateComplexGerm

variable {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {P : Model (2 * n) ≃L[ℝ] F} {A : Set E} {p : E}
  (g : NativeCoordinateComplexGerm P A p)

/-- A graph extension may start on any smaller real-open neighborhood.
Its correction produces the section germ consumed by the completion grading
producer. The original endomorphism germ is retained, and nonvanishing holds
throughout the produced neighborhood. -/
theorem exists_sectionGerm_of_graphExtension
    (W : TopologicalSpace.Opens E) (hW : (W : Set E) ⊆ g.bundlePatch.domain)
    (hpW : p ∈ W)
    (G : W → TotalSpace ℂ (fun z : W =>
      CanonicalTensorSquare ((g.bundlePatch.restrict W hW).complex z)))
    (hG : (g.bundlePatch.restrict W hW).IsSmoothBundleMap G)
    (hproj : ∀ z : W, z.val ∈ A → (G z).proj = z)
    (hnz : (G ⟨p, hpW⟩).snd ≠ 0) :
    ∃ h : NativeCoordinateCanonicalSectionGerm P A p,
      h.complexGerm = g ∧ (∀ z : h.domain, h.tensorSection z ≠ 0) ∧
      ∃ hsub : (h.domain : Set E) ⊆ W,
        ∀ (z : h.domain), z.val ∈ A →
          (canonicalSquareMap (h.patch.complex z) (h.tensorSection z)).val =
            (canonicalSquareMap ((g.bundlePatch.restrict W hW).complex
              (G ⟨z.val, hsub z.property⟩).proj) (G ⟨z.val, hsub z.property⟩).snd).val := by
  obtain ⟨V, hVc, hpV, σ, hs, hn, he⟩ :=
    (g.bundlePatch.restrict W hW).exists_nonzeroSection_of_bundleMap
      hpW g.mem_locus G hG hproj hnz
  let h : NativeCoordinateCanonicalSectionGerm P A p :=
    { complexGerm := g
      domain := V
      subset_bundlePatch := hVc.trans hW
      mem_domain := hpV
      tensorSection := σ
      smooth_section := hs
      nonzero_center := hn ⟨p, hpV⟩ }
  exact ⟨h, rfl, hn, hVc, he⟩

end NativeCoordinateComplexGerm

end FsFltz.Geometry
