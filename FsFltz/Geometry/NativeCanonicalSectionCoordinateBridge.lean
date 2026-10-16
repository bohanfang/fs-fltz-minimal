import FsFltz.Geometry.IntrinsicNativeCompletionGradingGraphExtensions

/-!
# Native canonical sections through spatial coordinate changes

Source: `geoemtric-part-fsf.tex`, smooth-extension convention, lines 119–122;
`def:maslov`, lines 212–232; `g:chain`, lines 407–413; and `sec:lean`,
lines 788–814. A section in an independently chosen native local
canonical-square bundle is transported through a supplied smooth invertible
spatial coordinate differential. Native bundle smoothness produces full
tensor regularity; inverse-coframe correction constructs a graph in the
consumer's independently selected complex patch, retaining every tensor
slot on the original locus. Neither a scalar extension nor a full-tensor
smoothness assumption nor a target graph is supplied.

This is a local coordinate-change foundation. The source native patch,
section, and differential are inputs. Constructing their original
completed-family atlas and identifying the differential with its original
interior and end chart derivatives remain separate obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry

variable {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pulling every slot through a varying smooth linear map is smooth.
The tensor and the slot map may both vary over the parameter base. -/
theorem contDiffOn_squaredTensor_coordinateChange
    {U : Set E} {S : E → SquaredCanonicalTensor n}
    {D : E → Model (2 * n) →L[ℝ] Model (2 * n)}
    (hS : ContDiffOn ℝ ∞ S U) (hD : ContDiffOn ℝ ∞ D U) :
    ContDiffOn ℝ ∞
      (fun z => (S z).compContinuousLinearMap (fun _ => D z)) U := by
  let L := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin n ⊕ Fin n => Model (2 * n))
    (fun _ : Fin n ⊕ Fin n => Model (2 * n)) ℂ
  exact (L.contDiff.comp_contDiffOn (contDiffOn_pi.mpr (fun _ => hD))).clm_apply hS

namespace NativeCoordinateCanonicalPatch

variable {K₀ : E → Model (2 * n) →L[ℝ] Model (2 * n)} {A : Set E}
  (c : NativeCoordinateCanonicalPatch (ContinuousLinearEquiv.refl ℝ (Model (2 * n))) K₀ A)

/-- Natural multiplication of a native section followed by all spatial
slots of an inverse coordinate differential, normalized by the target basis. -/
def coordinateTensor
    (σ : ∀ z : c.domain, CanonicalTensorSquare (c.complex z))
    (P : Model (2 * n) ≃L[ℝ] F) (D : E → F →L[ℝ] Model (2 * n))
    (z : E) : SquaredCanonicalTensor n :=
  (c.tensorExtension σ z).compContinuousLinearMap
    (fun _ => (D z).comp P.toContinuousLinearMap)

theorem coordinateTensor_apply
    (σ : ∀ z : c.domain, CanonicalTensorSquare (c.complex z))
    (P : Model (2 * n) ≃L[ℝ] F) (D : E → F →L[ℝ] Model (2 * n))
    {z : E} (hz : z ∈ c.domain) :
    c.coordinateTensor σ P D z =
      (canonicalSquareMap (c.complex ⟨z, hz⟩) (σ ⟨z, hz⟩)).val.compContinuousLinearMap
        (fun _ => (D z).comp P.toContinuousLinearMap) := by
  rw [coordinateTensor, c.tensorExtension_apply σ hz]
  ext v
  rfl

/-- Full transported tensor regularity follows from native source-section
smoothness. There is no tensor coefficient regularity input. -/
theorem smooth_coordinateTensor
    (σ : ∀ z : c.domain, CanonicalTensorSquare (c.complex z))
    (hσ : c.IsSmoothSection σ)
    (P : Model (2 * n) ≃L[ℝ] F) (D : E → F →L[ℝ] Model (2 * n))
    (hD : ContDiffOn ℝ ∞ D c.domain) :
    ContDiffOn ℝ ∞ (c.coordinateTensor σ P D) c.domain :=
  contDiffOn_squaredTensor_coordinateChange (c.smooth_tensorExtension σ hσ)
    (hD.clm_comp contDiffOn_const)

/-- A native source section and a supplied spatial coordinate law construct
the target graph germ. The complex equation and matching values are required
only on the original locus. The target bundle patch and its graph are output. -/
theorem exists_graphGerm_of_coordinateChange
    (σ : ∀ z : c.domain, CanonicalTensorSquare (c.complex z))
    (hσ : c.IsSmoothSection σ)
    (P : Model (2 * n) ≃L[ℝ] F) (D : E → F →L[ℝ] Model (2 * n))
    (hD : ContDiffOn ℝ ∞ D c.domain)
    (hDi : ∀ z ∈ c.domain, (D z).IsInvertible)
    (K : E → F →L[ℝ] F) (hK : ContDiffOn ℝ ∞ K c.domain)
    (hDK : ∀ (z : c.domain), z.val ∈ A → ∀ v,
      D z.val (K z.val v) = c.complex z (D z.val v))
    {p : E} (hp : p ∈ c.domain) (hpA : p ∈ A) (hnz : σ ⟨p, hp⟩ ≠ 0) :
    ∃ g : NativeCoordinateCanonicalGraphGerm P A p,
      g.complexGerm.field = K ∧ (g.domain : Set E) ⊆ c.domain ∧
      ∀ (z : g.domain), z.val ∈ A →
        (canonicalSquareMap (g.patch.complex (g.bundleMap z).proj)
          (g.bundleMap z).snd).val = c.coordinateTensor σ P D z.val := by
  have hKsq : ∀ z ∈ (c.domain : Set E) ∩ A, ∀ v, K z (K z v) = -v := by
    intro z hz v
    apply (hDi z hz.1).injective
    rw [hDK ⟨z, hz.1⟩ hz.2, hDK ⟨z, hz.1⟩ hz.2, c.complex_sq]
    simp
  let j : NativeCoordinateComplexGerm P A p :=
    ⟨c.domain, hp, hpA, K, hK, hKsq⟩
  let b := j.bundlePatch
  have hb : (b.domain : Set E) ⊆ c.domain := j.bundlePatch_subset
  let S := c.coordinateTensor σ P D
  have hS : ContDiffOn ℝ ∞ S b.domain := (c.smooth_coordinateTensor σ hσ P D hD).mono hb
  have hc : ∀ z, ∀ hz : z ∈ (b.domain : Set E) ∩ A,
      IsSquaredCanonicalTensor (b.complex ⟨z, hz.1⟩) (S z) := by
    intro z hz
    rw [b.complex_eq hz.2]
    change IsSquaredCanonicalTensor
      (P.symm.toContinuousLinearMap.comp ((K z).comp P.toContinuousLinearMap))
      (c.coordinateTensor σ P D z)
    rw [c.coordinateTensor_apply σ P D (hb hz.1)]
    apply isSquaredCanonicalTensor_comp_of_intertwines _
      (c.complex ⟨z, hb hz.1⟩) _ ?_
      _ (canonicalSquareMap _ (σ ⟨z, hb hz.1⟩)).property
    intro v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
    exact hDK ⟨z, hb hz.1⟩ hz.2 (P v)
  have hSnz : S p ≠ 0 := by
    let L := (D p).comp P.toContinuousLinearMap
    have hLi : L.IsInvertible := (hDi p hp).comp ⟨P, rfl⟩
    obtain ⟨e, heL⟩ := hLi
    intro hz
    apply c.tensorExtension_ne_zero σ hp hnz
    ext v
    have he := congrArg (fun T : SquaredCanonicalTensor n =>
      T (fun i => e.symm (v i))) hz
    change (c.tensorExtension σ p) (fun i => L (e.symm (v i))) = 0 at he
    rw [← heL] at he
    simpa only [ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, zero_apply] using he
  let q := fun z => canonicalCoframeCorrection (b.normalizedCoframe z) (S z)
  have hq : ContDiffOn ℝ ∞ q b.domain := contDiffOn_canonicalCoframeCorrection
    b.smooth_normalizedCoframe (fun z hz => b.invertible_normalizedCoframe hz) hS
  have hqc : ∀ z : b.domain, IsSquaredCanonicalTensor (b.complex z) (q z.val) := by
    intro z
    exact canonicalCoframeCorrection_canonical _ _
      (coframeComplexStructure_intertwines _ (b.invertible_normalizedCoframe z.property)) _
  have hqe : ∀ z, ∀ hz : z ∈ (b.domain : Set E) ∩ A, q z = S z := by
    intro z hz
    exact canonicalCoframeCorrection_eq _ (b.invertible_normalizedCoframe hz.1)
      (b.complex ⟨z, hz.1⟩)
      (coframeComplexStructure_intertwines _ (b.invertible_normalizedCoframe hz.1)) _ (hc z hz)
  let τ : ∀ z : b.domain, CanonicalTensorSquare (b.complex z) := fun z =>
    (canonicalSquareEquivOfComplexStructure _ (b.complex_sq z)).symm ⟨q z.val, hqc z⟩
  have hτ : ∀ z : b.domain, (canonicalSquareMap (b.complex z) (τ z)).val = q z.val := by
    intro z
    exact congrArg Subtype.val ((canonicalSquareEquivOfComplexStructure _
      (b.complex_sq z)).apply_symm_apply _)
  have hsτ : b.IsSmoothSection τ := by
    apply (verticalCanonicalTensorSquareSection_smooth_iff b.smooth_complex b.complex_sq τ).mpr
    simp_rw [hτ]
    intro z
    exact contMDiffAt_subtype_iff.mpr
      (contMDiffAt_iff_contDiffAt.mpr (hq.contDiffAt (b.domain.isOpen.mem_nhds z.property)))
  have hnτ : τ ⟨p, j.mem_bundlePatch⟩ ≠ 0 := by
    intro hz
    have he := hτ ⟨p, j.mem_bundlePatch⟩
    rw [hz, map_zero, Submodule.coe_zero, hqe p ⟨j.mem_bundlePatch, hpA⟩] at he
    exact hSnz he.symm
  let g : NativeCoordinateCanonicalGraphGerm P A p :=
    { complexGerm := j
      domain := b.domain
      subset_bundlePatch := Subset.refl _
      mem_domain := j.mem_bundlePatch
      bundleMap := fun z => ⟨z, τ z⟩
      smooth_bundleMap := hsτ
      projection_locus := fun _ _ => rfl
      nonzero_center := hnτ }
  refine ⟨g, rfl, hb, ?_⟩
  intro z hzA
  exact (hτ z).trans (hqe z.val ⟨z.property, hzA⟩)

/-- The graph constructed from the source section is consumed by native
graph rectification. The resulting target section is nonzero on its whole
neighborhood and recovers the complete unnormalized spatial tensor. -/
theorem exists_sectionGerm_of_coordinateChange
    (σ : ∀ z : c.domain, CanonicalTensorSquare (c.complex z))
    (hσ : c.IsSmoothSection σ)
    (P : Model (2 * n) ≃L[ℝ] F) (D : E → F →L[ℝ] Model (2 * n))
    (hD : ContDiffOn ℝ ∞ D c.domain)
    (hDi : ∀ z ∈ c.domain, (D z).IsInvertible)
    (K : E → F →L[ℝ] F) (hK : ContDiffOn ℝ ∞ K c.domain)
    (hDK : ∀ (z : c.domain), z.val ∈ A → ∀ v,
      D z.val (K z.val v) = c.complex z (D z.val v))
    {p : E} (hp : p ∈ c.domain) (hpA : p ∈ A) (hnz : σ ⟨p, hp⟩ ≠ 0) :
    ∃ h : NativeCoordinateCanonicalSectionGerm P A p,
      h.complexGerm.field = K ∧ (h.domain : Set E) ⊆ c.domain ∧
      (∀ z : h.domain, h.tensorSection z ≠ 0) ∧
      ∀ (z : h.domain), z.val ∈ A →
        h.tensor z.val = (c.tensorExtension σ z.val).compContinuousLinearMap
          (fun _ => D z.val) := by
  obtain ⟨g, hgK, hgc, hgT⟩ :=
    c.exists_graphGerm_of_coordinateChange σ hσ P D hD hDi K hK hDK hp hpA hnz
  obtain ⟨h, heJ, hn, hsub, heT⟩ := g.exists_sectionGerm
  refine ⟨h, ?_, hsub.trans hgc, hn, ?_⟩
  · rw [heJ]
    exact hgK
  · intro z hzA
    apply h.patch.tensorExtension_eq_of_normalized h.tensorSection z.property
    have hm := (heT z hzA).trans (hgT ⟨z.val, hsub z.property⟩ hzA)
    exact hm.trans (by
      ext v
      simp only [coordinateTensor, ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousLinearMap.comp_apply])

end NativeCoordinateCanonicalPatch

/-- Spatial differential of a local parameter-dependent coordinate map.
The time direction is excluded from the canonical tensor's slots. -/
def spatialCoordinateDerivative
    (φ : ℝ × F → Model (2 * n)) (z : ℝ × F) : F →L[ℝ] Model (2 * n) :=
  (fderiv ℝ φ z).comp (ContinuousLinearMap.inr ℝ ℝ F)

theorem spatialCoordinateDerivative_eq
    (φ : ℝ × F → Model (2 * n)) {z : ℝ × F}
    (hφ : DifferentiableAt ℝ φ z) :
    spatialCoordinateDerivative φ z = fderiv ℝ (fun y => φ (z.1, y)) z.2 := by
  have hi : HasFDerivAt (fun y : F => (z.1, y))
      (ContinuousLinearMap.inr ℝ ℝ F) z.2 :=
    (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  exact (hφ.hasFDerivAt.comp z.2 hi).fderiv.symm

/-- Smoothness of the actual spatial derivative is derived on the local
open domain; no global time extension or derivative regularity is assumed. -/
theorem contDiffOn_spatialCoordinateDerivative
    {U : Set (ℝ × F)} (hU : IsOpen U) (φ : ℝ × F → Model (2 * n))
    (hφ : ContDiffOn ℝ ∞ φ U) :
    ContDiffOn ℝ ∞ (spatialCoordinateDerivative φ) U :=
  (hφ.fderiv_of_isOpen hU (by simp)).clm_comp contDiffOn_const

namespace NativeCoordinateCanonicalPatch

variable {K₀ : (ℝ × F) → Model (2 * n) →L[ℝ] Model (2 * n)}
  {A : Set (ℝ × F)}
  (c : NativeCoordinateCanonicalPatch (ContinuousLinearEquiv.refl ℝ (Model (2 * n))) K₀ A)

/-- An actual local spatial coordinate map supplies the graph producer's
differential and its regularity. The full tensor matching uses its literal
spatial derivative, including at the original parameter endpoints. -/
theorem exists_graphGerm_of_spatialCoordinateMap
    (σ : ∀ z : c.domain, CanonicalTensorSquare (c.complex z))
    (hσ : c.IsSmoothSection σ) (P : Model (2 * n) ≃L[ℝ] F)
    (φ : ℝ × F → Model (2 * n)) (hφ : ContDiffOn ℝ ∞ φ c.domain)
    (hφi : ∀ z ∈ c.domain, (fderiv ℝ (fun y => φ (z.1, y)) z.2).IsInvertible)
    (K : (ℝ × F) → F →L[ℝ] F) (hK : ContDiffOn ℝ ∞ K c.domain)
    (hφK : ∀ (z : c.domain), z.val ∈ A → ∀ v,
      fderiv ℝ (fun y => φ (z.val.1, y)) z.val.2 (K z.val v) =
        c.complex z (fderiv ℝ (fun y => φ (z.val.1, y)) z.val.2 v))
    {p : ℝ × F} (hp : p ∈ c.domain) (hpA : p ∈ A) (hnz : σ ⟨p, hp⟩ ≠ 0) :
    ∃ g : NativeCoordinateCanonicalGraphGerm P A p,
      g.complexGerm.field = K ∧ (g.domain : Set (ℝ × F)) ⊆ c.domain ∧
      ∀ (z : g.domain), z.val ∈ A →
        (canonicalSquareMap (g.patch.complex (g.bundleMap z).proj)
          (g.bundleMap z).snd).val =
          (c.tensorExtension σ z.val).compContinuousLinearMap
            (fun _ => (fderiv ℝ (fun y => φ (z.val.1, y)) z.val.2).comp
              P.toContinuousLinearMap) := by
  have hd : ∀ z ∈ c.domain, spatialCoordinateDerivative φ z =
      fderiv ℝ (fun y => φ (z.1, y)) z.2 := by
    intro z hz
    exact spatialCoordinateDerivative_eq φ
      ((hφ.contDiffAt (c.domain.isOpen.mem_nhds hz)).differentiableAt (by simp))
  obtain ⟨g, hgK, hgc, hgT⟩ :=
    c.exists_graphGerm_of_coordinateChange σ hσ P (spatialCoordinateDerivative φ)
      (contDiffOn_spatialCoordinateDerivative c.domain.isOpen φ hφ)
      (fun z hz => hd z hz ▸ hφi z hz) K hK
      (fun z hz v => by rw [hd z.val z.property]; exact hφK z hz v) hp hpA hnz
  refine ⟨g, hgK, hgc, ?_⟩
  intro z hzA
  rw [hgT z hzA, coordinateTensor, hd z.val (hgc z.property)]

/-- The actual coordinate-map graph route produces a nonvanishing target
section germ with the complete original unnormalized derivative pullback. -/
theorem exists_sectionGerm_of_spatialCoordinateMap
    (σ : ∀ z : c.domain, CanonicalTensorSquare (c.complex z))
    (hσ : c.IsSmoothSection σ) (P : Model (2 * n) ≃L[ℝ] F)
    (φ : ℝ × F → Model (2 * n)) (hφ : ContDiffOn ℝ ∞ φ c.domain)
    (hφi : ∀ z ∈ c.domain, (fderiv ℝ (fun y => φ (z.1, y)) z.2).IsInvertible)
    (K : (ℝ × F) → F →L[ℝ] F) (hK : ContDiffOn ℝ ∞ K c.domain)
    (hφK : ∀ (z : c.domain), z.val ∈ A → ∀ v,
      fderiv ℝ (fun y => φ (z.val.1, y)) z.val.2 (K z.val v) =
        c.complex z (fderiv ℝ (fun y => φ (z.val.1, y)) z.val.2 v))
    {p : ℝ × F} (hp : p ∈ c.domain) (hpA : p ∈ A) (hnz : σ ⟨p, hp⟩ ≠ 0) :
    ∃ h : NativeCoordinateCanonicalSectionGerm P A p,
      h.complexGerm.field = K ∧ (h.domain : Set (ℝ × F)) ⊆ c.domain ∧
      (∀ z : h.domain, h.tensorSection z ≠ 0) ∧
      ∀ (z : h.domain), z.val ∈ A →
        h.tensor z.val = (c.tensorExtension σ z.val).compContinuousLinearMap
          (fun _ => fderiv ℝ (fun y => φ (z.val.1, y)) z.val.2) := by
  obtain ⟨g, hgK, hgc, hgT⟩ :=
    c.exists_graphGerm_of_spatialCoordinateMap σ hσ P φ hφ hφi K hK hφK hp hpA hnz
  obtain ⟨h, heJ, hn, hsub, heT⟩ := g.exists_sectionGerm
  refine ⟨h, ?_, hsub.trans hgc, hn, ?_⟩
  · rw [heJ]
    exact hgK
  · intro z hzA
    apply h.patch.tensorExtension_eq_of_normalized h.tensorSection z.property
    have hm := (heT z hzA).trans (hgT ⟨z.val, hsub z.property⟩ hzA)
    exact hm.trans (by
      ext v
      simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousLinearMap.comp_apply])

end NativeCoordinateCanonicalPatch
end FsFltz.Geometry
