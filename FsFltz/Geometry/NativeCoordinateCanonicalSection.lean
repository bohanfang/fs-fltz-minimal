import FsFltz.Geometry.CoordinateComplexCoframe
import FsFltz.Geometry.VerticalCanonicalBundle
import FsFltz.Geometry.CompatibleComplexExtension

/-!
# Native local canonical-square sections and source tensor extensions

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–232, and
`sec:lean`, lines 794–814. A real smooth extension of a source complex
endomorphism is corrected to a genuine complex structure on a smaller open
patch. The correction retains every value on the prescribed locus; the
endomorphism is required to square to minus one only on that locus.

An actual smooth section of the native vertical canonical-square bundle on
this patch produces a smooth full tensor in the original tangent model.
Section smoothness uses the existing bundle topology and `ContMDiff`, rather
than a smoothness assumption on the tensor image. Existence of an extending
native section for arbitrary interval bundle data is a separate bridge.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Bundle

namespace FsFltz.Geometry

variable {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A source patch carries an extending coframe. It represents the original
complex endomorphism only on the prescribed locus. -/
structure NativeCoordinateCanonicalPatch (P : Model (2 * n) ≃L[ℝ] F)
    (K : E → F →L[ℝ] F) (A : Set E) where
  domain : TopologicalSpace.Opens E
  coframe : E → F →L[ℝ] TangentCoordinates n
  smooth_coframe : ContDiffOn ℝ ∞ coframe domain
  invertible_coframe : ∀ z ∈ domain, (coframe z).IsInvertible
  intertwines : ∀ z ∈ (domain : Set E) ∩ A, ∀ v,
    coframe z (K z v) = coordinateComplexStructure n (coframe z v)

/-- The original endomorphism extension produces its native complex bundle
patch; a coframe and an off-locus complex structure are conclusions. -/
theorem exists_nativeCoordinateCanonicalPatch
    (P : Model (2 * n) ≃L[ℝ] F) {K : E → F →L[ℝ] F}
    {U A : Set E} {p : E} (hU : IsOpen U) (hpU : p ∈ U) (hpA : p ∈ A)
    (hK : ContDiffOn ℝ ∞ K U)
    (hsq : ∀ z ∈ U ∩ A, ∀ v, K z (K z v) = -v) :
    ∃ c : NativeCoordinateCanonicalPatch P K A,
      (c.domain : Set E) ⊆ U ∧ p ∈ c.domain := by
  obtain ⟨V, hVU, hVo, hpV, B, hB, hBi, hBJ⟩ :=
    exists_smooth_local_coordinateComplexCoframe P hU hpU hpA K hK hsq
  exact ⟨⟨⟨V, hVo⟩, B, hB, hBi, hBJ⟩, hVU, hpV⟩

namespace NativeCoordinateCanonicalPatch

variable {P : Model (2 * n) ≃L[ℝ] F} {K : E → F →L[ℝ] F} {A : Set E}
  (c : NativeCoordinateCanonicalPatch P K A)

/-- A section extension may be defined on any smaller neighborhood of its
center; no extension over the whole initially constructed patch is needed. -/
def restrict (V : TopologicalSpace.Opens E) (hV : (V : Set E) ⊆ c.domain) :
    NativeCoordinateCanonicalPatch P K A where
  domain := V
  coframe := c.coframe
  smooth_coframe := c.smooth_coframe.mono hV
  invertible_coframe := fun z hz => c.invertible_coframe z (hV hz)
  intertwines := fun z hz => c.intertwines z ⟨hV hz.1, hz.2⟩

def normalizedCoframe (z : E) : Model (2 * n) →L[ℝ] TangentCoordinates n :=
  (c.coframe z).comp P.toContinuousLinearMap

theorem smooth_normalizedCoframe : ContDiffOn ℝ ∞ c.normalizedCoframe c.domain :=
  c.smooth_coframe.clm_comp contDiffOn_const

theorem invertible_normalizedCoframe {z : E} (hz : z ∈ c.domain) :
    (c.normalizedCoframe z).IsInvertible :=
  (c.invertible_coframe z hz).comp ⟨P, rfl⟩

/-- The correcting complex structure exists on the whole local open patch,
although the original endomorphism laws are only prescribed on `A`. -/
def complex (z : c.domain) : Model (2 * n) →L[ℝ] Model (2 * n) :=
  coframeComplexStructure (c.normalizedCoframe z.val)

theorem smooth_complex : ContMDiff 𝓘(ℝ, E)
    𝓘(ℝ, Model (2 * n) →L[ℝ] Model (2 * n)) ∞ c.complex := by
  intro z
  change ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Model (2 * n) →L[ℝ] Model (2 * n)) ∞
    (fun z : c.domain => coframeComplexStructure (c.normalizedCoframe z.val)) z
  apply (contMDiffAt_subtype_iff
    (f := fun z : E => coframeComplexStructure (c.normalizedCoframe z))).mpr
  exact contMDiffAt_iff_contDiffAt.mpr
    ((contDiffOn_coframeComplexStructure c.smooth_normalizedCoframe
      (fun z hz => c.invertible_normalizedCoframe hz)).contDiffAt
        (c.domain.isOpen.mem_nhds z.property))

theorem complex_sq (z : c.domain) (v : Model (2 * n)) :
    c.complex z (c.complex z v) = -v :=
  coframeComplexStructure_sq _ (c.invertible_normalizedCoframe z.property) v

/-- Correction agrees literally with the normalized original field. -/
theorem complex_eq {z : c.domain} (hzA : z.val ∈ A) :
    c.complex z =
      P.symm.toContinuousLinearMap.comp ((K z.val).comp P.toContinuousLinearMap) := by
  apply coframeComplexStructure_eq _ (c.invertible_normalizedCoframe z.property)
  intro v
  simpa only [normalizedCoframe, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using
      c.intertwines z.val ⟨z.property, hzA⟩ (P v)

/-- Actual native section smoothness in the independently constructed
canonical-square bundle on the real open patch. -/
def IsSmoothSection (σ : ∀ z : c.domain, CanonicalTensorSquare (c.complex z)) : Prop :=
  let a := verticalCanonicalTensorSquareVectorPrebundle c.smooth_complex c.complex_sq
  letI := a.totalSpaceTopology
  letI := a.toFiberBundle
  ContMDiff 𝓘(ℝ, E) ((𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) ∞
    (fun z => (⟨z, σ z⟩ : Bundle.TotalSpace ℂ
      (fun z : c.domain => CanonicalTensorSquare (c.complex z))))

open scoped Classical in
/-- Natural square multiplication, transported to the original tangent
model. Its value outside this local patch is immaterial. -/
def tensorExtension (σ : ∀ z : c.domain, CanonicalTensorSquare (c.complex z))
    (z : E) : ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => F) ℂ :=
  if hz : z ∈ c.domain then
    (canonicalSquareMap (c.complex ⟨z, hz⟩) (σ ⟨z, hz⟩)).val.compContinuousLinearMap
      (fun _ => P.symm.toContinuousLinearMap)
  else 0

theorem tensorExtension_apply
    (σ : ∀ z : c.domain, CanonicalTensorSquare (c.complex z))
    {z : E} (hz : z ∈ c.domain) :
    c.tensorExtension σ z =
      (canonicalSquareMap (c.complex ⟨z, hz⟩) (σ ⟨z, hz⟩)).val.compContinuousLinearMap
        (fun _ => P.symm.toContinuousLinearMap) := by
  simp only [tensorExtension, hz, ↓reduceDIte]

/-- Bundle smoothness supplies full tensor smoothness, using the proved
native-section/tensor correspondence; no tensor regularity is supplied. -/
theorem smooth_tensorExtension
    (σ : ∀ z : c.domain, CanonicalTensorSquare (c.complex z))
    (hσ : c.IsSmoothSection σ) : ContDiffOn ℝ ∞ (c.tensorExtension σ) c.domain := by
  have h := (verticalCanonicalTensorSquareSection_smooth_iff
    c.smooth_complex c.complex_sq σ).mp hσ
  have hcomp : ContMDiff 𝓘(ℝ, E)
      𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => F) ℂ) ∞
      (fun z : c.domain =>
        (canonicalSquareMap (c.complex z) (σ z)).val.compContinuousLinearMap
          (fun _ => P.symm.toContinuousLinearMap)) := by
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n ⊕ Fin n => P.symm.toContinuousLinearMap)).contDiff.contMDiff.comp h
  intro z hz
  have hzσ := hcomp ⟨z, hz⟩
  have heq : (fun w : c.domain => c.tensorExtension σ w.val) =
      (fun w : c.domain =>
        (canonicalSquareMap (c.complex w) (σ w)).val.compContinuousLinearMap
          (fun _ => P.symm.toContinuousLinearMap)) :=
    funext (fun w => c.tensorExtension_apply σ w.property)
  rw [← heq] at hzσ
  exact ((contMDiffAt_subtype_iff.mp hzσ).contDiffAt).contDiffWithinAt

theorem tensorExtension_normalized
    (σ : ∀ z : c.domain, CanonicalTensorSquare (c.complex z)) {z : E} (hz : z ∈ c.domain) :
    (c.tensorExtension σ z).compContinuousLinearMap (fun _ => P.toContinuousLinearMap) =
      (canonicalSquareMap (c.complex ⟨z, hz⟩) (σ ⟨z, hz⟩)).val := by
  rw [c.tensorExtension_apply σ hz]
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

theorem tensorExtension_canonical
    (σ : ∀ z : c.domain, CanonicalTensorSquare (c.complex z)) {z : E}
    (hz : z ∈ c.domain) (hzA : z ∈ A) :
    IsSquaredCanonicalTensor
      (P.symm.toContinuousLinearMap.comp ((K z).comp P.toContinuousLinearMap))
      ((c.tensorExtension σ z).compContinuousLinearMap (fun _ => P.toContinuousLinearMap)) := by
  rw [c.tensorExtension_normalized σ hz, ← c.complex_eq (z := ⟨z, hz⟩) hzA]
  exact (canonicalSquareMap _ (σ ⟨z, hz⟩)).property

theorem tensorExtension_ne_zero
    (σ : ∀ z : c.domain, CanonicalTensorSquare (c.complex z)) {z : E}
    (hz : z ∈ c.domain) (hnz : σ ⟨z, hz⟩ ≠ 0) : c.tensorExtension σ z ≠ 0 := by
  intro hzero
  apply hnz
  apply (canonicalSquareMap_bijective _ (c.complex_sq ⟨z, hz⟩)).1
  rw [map_zero]
  apply Subtype.ext
  have he := c.tensorExtension_normalized σ hz
  rw [hzero] at he
  ext v
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    zero_apply, Submodule.coe_zero] using
      congrArg (fun T => T v) he.symm

/-- Matching in the normalized native bundle recovers the full original
source-coordinate tensor, without a separate tensor-coordinate assumption. -/
theorem tensorExtension_eq_of_normalized
    (σ : ∀ z : c.domain, CanonicalTensorSquare (c.complex z)) {z : E}
    (hz : z ∈ c.domain)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => F) ℂ)
    (hT : (canonicalSquareMap (c.complex ⟨z, hz⟩) (σ ⟨z, hz⟩)).val =
      T.compContinuousLinearMap (fun _ => P.toContinuousLinearMap)) :
    c.tensorExtension σ z = T := by
  have he := (c.tensorExtension_normalized σ hz).trans hT
  ext v
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using
      congrArg (fun T => T (fun i => P.symm (v i))) he

end NativeCoordinateCanonicalPatch

/-- A real smooth germ of the original complex endomorphism, subject to
the complex equation only on the prescribed source locus. -/
structure NativeCoordinateComplexGerm (P : Model (2 * n) ≃L[ℝ] F)
    (A : Set E) (p : E) where
  domain : TopologicalSpace.Opens E
  mem_domain : p ∈ domain
  mem_locus : p ∈ A
  field : E → F →L[ℝ] F
  smooth_field : ContDiffOn ℝ ∞ field domain
  square : ∀ z ∈ (domain : Set E) ∩ A, ∀ v, field z (field z v) = -v

namespace NativeCoordinateComplexGerm

variable {P : Model (2 * n) ≃L[ℝ] F} {A : Set E} {p : E}
  (g : NativeCoordinateComplexGerm P A p)

/-- This patch is produced from the original endomorphism germ. -/
def bundlePatch : NativeCoordinateCanonicalPatch P g.field A :=
  (exists_nativeCoordinateCanonicalPatch P g.domain.isOpen g.mem_domain g.mem_locus
    g.smooth_field g.square).choose

theorem bundlePatch_subset : (g.bundlePatch.domain : Set E) ⊆ g.domain :=
  (exists_nativeCoordinateCanonicalPatch P g.domain.isOpen g.mem_domain g.mem_locus
    g.smooth_field g.square).choose_spec.1

theorem mem_bundlePatch : p ∈ g.bundlePatch.domain :=
  (exists_nativeCoordinateCanonicalPatch P g.domain.isOpen g.mem_domain g.mem_locus
    g.smooth_field g.square).choose_spec.2

end NativeCoordinateComplexGerm

/-- An extending native canonical-square section on a neighborhood in the
bundle produced from its original endomorphism germ. Its regularity is native
bundle `ContMDiff`; it does not supply a full tensor extension. -/
structure NativeCoordinateCanonicalSectionGerm (P : Model (2 * n) ≃L[ℝ] F)
    (A : Set E) (p : E) where
  complexGerm : NativeCoordinateComplexGerm P A p
  domain : TopologicalSpace.Opens E
  subset_bundlePatch : (domain : Set E) ⊆ complexGerm.bundlePatch.domain
  mem_domain : p ∈ domain
  tensorSection : ∀ z : domain,
    CanonicalTensorSquare
      ((complexGerm.bundlePatch.restrict domain subset_bundlePatch).complex z)
  smooth_section : (complexGerm.bundlePatch.restrict domain subset_bundlePatch).IsSmoothSection tensorSection
  nonzero_center : tensorSection ⟨p, mem_domain⟩ ≠ 0

namespace NativeCoordinateCanonicalSectionGerm

variable {P : Model (2 * n) ≃L[ℝ] F} {A : Set E} {p : E}
  (g : NativeCoordinateCanonicalSectionGerm P A p)

def patch : NativeCoordinateCanonicalPatch P g.complexGerm.field A :=
  g.complexGerm.bundlePatch.restrict g.domain g.subset_bundlePatch

def tensor : E → ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => F) ℂ :=
  g.patch.tensorExtension g.tensorSection

theorem smooth_field : ContDiffOn ℝ ∞ g.complexGerm.field g.domain :=
  g.complexGerm.smooth_field.mono
    (g.subset_bundlePatch.trans g.complexGerm.bundlePatch_subset)

theorem smooth_tensor : ContDiffOn ℝ ∞ g.tensor g.domain :=
  g.patch.smooth_tensorExtension g.tensorSection g.smooth_section

theorem tensor_canonical {z : E} (hz : z ∈ g.domain) (hzA : z ∈ A) :
    IsSquaredCanonicalTensor
      (P.symm.toContinuousLinearMap.comp ((g.complexGerm.field z).comp P.toContinuousLinearMap))
      ((g.tensor z).compContinuousLinearMap (fun _ => P.toContinuousLinearMap)) :=
  g.patch.tensorExtension_canonical g.tensorSection hz hzA

theorem tensor_nonzero_center : g.tensor p ≠ 0 :=
  g.patch.tensorExtension_ne_zero g.tensorSection g.mem_domain g.nonzero_center

end NativeCoordinateCanonicalSectionGerm
end FsFltz.Geometry
