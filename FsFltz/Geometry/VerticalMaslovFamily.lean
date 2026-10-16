import FsFltz.Geometry.VerticalCanonicalBundle
import FsFltz.Geometry.MaslovHomotopy

/-!
# Native vertical canonical-square sections of parameter families

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–232;
`thm:target` / `g:chain`, lines 407–413; `sec:lean`, lines 794–814.

The vertical bundle on a parameter–spatial chart has fiber
`K_{J(t,x)} ⊗ K_{J(t,x)}` and base the open subset of
`ℝ × Model (2n)`. The parameter tangent is excluded. Native section
smoothness is identified with joint smoothness of the actual squared
canonical tensor by the independently constructed vertical atlas.

The original family admits this exact correspondence on interior time
charts. A smooth endpoint-preserving change of time gives a complex
structure on the whole time axis and native sections on whole-time spatial
charts, including the endpoint fibers. Both the section and the complex
structure use the same change of time. For a varying ambient two-form that
two-form must be changed in time as well; this does not assert a lift on
the original prescribed geometric deformation.

`IntrinsicVerticalCanonicalBundle` glues these spatial charts through their
tangent-transition maps and proves native smoothness of the resulting
whole-time section. The unchanged prescribed-family endpoint bridge remains
separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Bundle

namespace FsFltz.Geometry

private theorem contMDiff_open_restrict_iff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : TopologicalSpace.Opens E) (f : E → F) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (fun x : U => f x) ↔
      ContDiffOn ℝ ∞ f U := by
  constructor
  · intro h x hx
    exact (contMDiffAt_subtype_iff.mp (h ⟨x, hx⟩)).contDiffAt.contDiffWithinAt
  · intro h x
    exact contMDiffAt_subtype_iff.mpr
      (contMDiffAt_iff_contDiffAt.mpr (h.contDiffAt (U.isOpen.mem_nhds x.property)))

/-- A time-open spatial coordinate domain. Its model has one parameter
direction in addition to the `2n` vertical directions. -/
def parameterSpatialChartDomain {n : ℕ} (M : SmoothManifold (2 * n))
    (a : M.Point) (A : TopologicalSpace.Opens ℝ) :
    TopologicalSpace.Opens (ℝ × Model (2 * n)) :=
  ⟨(A : Set ℝ) ×ˢ (chartAt (Model (2 * n)) a).target,
    A.isOpen.prod (chartAt (Model (2 * n)) a).open_target⟩

def parameterChartComplexStructure {n : ℕ} (M : SmoothManifold (2 * n))
    (J : ℝ → AlmostComplexField M) (a : M.Point) (A : TopologicalSpace.Opens ℝ)
    (p : parameterSpatialChartDomain M a A) : Model (2 * n) →L[ℝ] Model (2 * n) :=
  almostComplexInChart M a (J p.val.1) p.val.2

theorem parameterChartComplexStructure_smooth {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : ℝ → AlmostComplexField M)
    (a : M.Point) (A : TopologicalSpace.Opens ℝ)
    (hJ : ContDiffOn ℝ ∞ (fun p => almostComplexInChart M a (J p.1) p.2)
      (parameterSpatialChartDomain M a A : Set (ℝ × Model (2 * n)))) :
    ContMDiff 𝓘(ℝ, ℝ × Model (2 * n))
      𝓘(ℝ, Model (2 * n) →L[ℝ] Model (2 * n)) ∞
      (parameterChartComplexStructure M J a A) :=
  (contMDiff_open_restrict_iff _ _).mpr hJ

theorem parameterChartComplexStructure_sq {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : ℝ → AlmostComplexField M)
    (a : M.Point) (A : TopologicalSpace.Opens ℝ)
    (hJsq : ∀ t ∈ A, ∀ x v, J t x (J t x v) = -v)
    (p : parameterSpatialChartDomain M a A) (v : Model (2 * n)) :
    parameterChartComplexStructure M J a A p
      (parameterChartComplexStructure M J a A p v) = -v :=
  almostComplexInChart_sq M a (J p.val.1) (hJsq p.val.1 p.property.1)
    p.val.2 p.property.2 v

/-- The actual canonical tensor square in a parameter–spatial chart.
Its image is the spatial tangent pullback of the original actual tensor. -/
def parameterChartTensorSquareSection {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : ℝ → AlmostComplexField M)
    (s : ℝ → M.Point → SquaredCanonicalTensor n)
    (a : M.Point) (A : TopologicalSpace.Opens ℝ)
    (hJsq : ∀ t ∈ A, ∀ x v, J t x (J t x v) = -v)
    (hcanonical : ∀ t ∈ A, ∀ x, IsSquaredCanonicalTensor (J t x) (s t x))
    (p : parameterSpatialChartDomain M a A) :
    CanonicalTensorSquare (parameterChartComplexStructure M J a A p) :=
  (canonicalSquareEquivOfComplexStructure _
    (parameterChartComplexStructure_sq M J a A hJsq p)).symm
      ⟨squaredTensorInChart M a (s p.val.1) p.val.2,
        squaredTensorInChart_canonical M a (J p.val.1) (s p.val.1)
          (hcanonical p.val.1 p.property.1) p.val.2 p.property.2⟩

theorem canonicalSquareMap_parameterChartTensorSquareSection {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : ℝ → AlmostComplexField M)
    (s : ℝ → M.Point → SquaredCanonicalTensor n)
    (a : M.Point) (A : TopologicalSpace.Opens ℝ)
    (hJsq : ∀ t ∈ A, ∀ x v, J t x (J t x v) = -v)
    (hcanonical : ∀ t ∈ A, ∀ x, IsSquaredCanonicalTensor (J t x) (s t x))
    (p : parameterSpatialChartDomain M a A) :
    (canonicalSquareMap (parameterChartComplexStructure M J a A p)
      (parameterChartTensorSquareSection M J s a A hJsq hcanonical p)).val =
      squaredTensorInChart M a (s p.val.1) p.val.2 :=
  congrArg Subtype.val ((canonicalSquareEquivOfComplexStructure _
    (parameterChartComplexStructure_sq M J a A hJsq p)).apply_symm_apply _)

/-- Exact original-family correspondence on any open time domain where
the structures remain complex. No time reparametrization occurs here. -/
theorem parameterChartTensorSquareSection_smooth_iff {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : ℝ → AlmostComplexField M)
    (s : ℝ → M.Point → SquaredCanonicalTensor n)
    (a : M.Point) (A : TopologicalSpace.Opens ℝ)
    (hJ : ContDiffOn ℝ ∞ (fun p => almostComplexInChart M a (J p.1) p.2)
      (parameterSpatialChartDomain M a A : Set (ℝ × Model (2 * n))))
    (hJsq : ∀ t ∈ A, ∀ x v, J t x (J t x v) = -v)
    (hcanonical : ∀ t ∈ A, ∀ x, IsSquaredCanonicalTensor (J t x) (s t x)) :
    let hK := parameterChartComplexStructure_smooth M J a A hJ
    let hKsq := parameterChartComplexStructure_sq M J a A hJsq
    let b := verticalCanonicalTensorSquareVectorPrebundle hK hKsq
    letI := b.totalSpaceTopology
    letI := b.toFiberBundle
    ContMDiff 𝓘(ℝ, ℝ × Model (2 * n))
      ((𝓘(ℝ, ℝ × Model (2 * n))).prod 𝓘(ℝ, ℂ)) ∞
      (fun p => (⟨p, parameterChartTensorSquareSection M J s a A hJsq hcanonical p⟩ :
        TotalSpace ℂ (fun p : parameterSpatialChartDomain M a A =>
          CanonicalTensorSquare (parameterChartComplexStructure M J a A p)))) ↔
      ContDiffOn ℝ ∞ (fun p => squaredTensorInChart M a (s p.1) p.2)
        (parameterSpatialChartDomain M a A : Set (ℝ × Model (2 * n))) := by
  dsimp only
  let hK := parameterChartComplexStructure_smooth M J a A hJ
  let hKsq := parameterChartComplexStructure_sq M J a A hJsq
  let b := verticalCanonicalTensorSquareVectorPrebundle hK hKsq
  let := b.totalSpaceTopology
  let := b.toFiberBundle
  have hi := verticalCanonicalTensorSquareSection_smooth_iff hK hKsq
    (parameterChartTensorSquareSection M J s a A hJsq hcanonical)
  dsimp only at hi
  rw [hi]
  simp_rw [canonicalSquareMap_parameterChartTensorSquareSection]
  exact contMDiff_open_restrict_iff (parameterSpatialChartDomain M a A)
    (fun p => squaredTensorInChart M a (s p.1) p.2)

namespace SmoothNearInterval

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_interior {s : Set E} {f : ℝ × E → F}
    (hf : SmoothNearInterval s f) : ContDiffOn ℝ ∞ f (Ioo (0 : ℝ) 1 ×ˢ s) := by
  rcases hf with ⟨U, _, hsub, hs⟩
  exact hs.mono (fun p hp => hsub ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2⟩)

/-- Reparametrizing all time-dependent data by the same endpoint-preserving
smooth map gives joint regularity on the entire time axis. -/
theorem contDiffOn_smoothTransition {s : Set E} {f : ℝ × E → F}
    (hf : SmoothNearInterval s f) :
    ContDiffOn ℝ ∞ (fun p => f (Real.smoothTransition p.1, p.2)) (univ ×ˢ s) := by
  rcases hf with ⟨U, _, hsub, hs⟩
  exact hs.comp ((Real.smoothTransition.contDiff.comp contDiff_fst).prodMk
    contDiff_snd).contDiffOn (fun p hp =>
      hsub ⟨⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, hp.2⟩)

end SmoothNearInterval

def interiorTimeDomain : TopologicalSpace.Opens ℝ := ⟨Ioo 0 1, isOpen_Ioo⟩

namespace MaslovFamily

variable {n : ℕ} {M : SmoothManifold (2 * n)} {eta : ℝ → M.Form 2}

def interiorChartSection (f : MaslovFamily M eta) (a : M.Point) :=
  parameterChartTensorSquareSection M f.J f.tensor a interiorTimeDomain
    (fun t ht => (f.compatible t ⟨ht.1.le, ht.2.le⟩).2.1)
    (fun t ht => f.canonical t ⟨ht.1.le, ht.2.le⟩)

/-- The exact prescribed family yields actual native smooth vertical
canonical-square sections on its interior parameter–spatial charts. -/
theorem interiorChartSection_smooth (f : MaslovFamily M eta) (a : M.Point) :
    let hJ := parameterChartComplexStructure_smooth M f.J a interiorTimeDomain
      (f.smoothJ a).contDiffOn_interior
    let hJsq := parameterChartComplexStructure_sq M f.J a interiorTimeDomain
      (fun t ht => (f.compatible t ⟨ht.1.le, ht.2.le⟩).2.1)
    let b := verticalCanonicalTensorSquareVectorPrebundle hJ hJsq
    letI := b.totalSpaceTopology
    letI := b.toFiberBundle
    ContMDiff 𝓘(ℝ, ℝ × Model (2 * n))
      ((𝓘(ℝ, ℝ × Model (2 * n))).prod 𝓘(ℝ, ℂ)) ∞
      (fun p => (⟨p, f.interiorChartSection a p⟩ :
        TotalSpace ℂ (fun p : parameterSpatialChartDomain M a interiorTimeDomain =>
          CanonicalTensorSquare (parameterChartComplexStructure M f.J a
            interiorTimeDomain p)))) :=
  (parameterChartTensorSquareSection_smooth_iff M f.J f.tensor a interiorTimeDomain
    (f.smoothJ a).contDiffOn_interior
    (fun t ht => (f.compatible t ⟨ht.1.le, ht.2.le⟩).2.1)
    (fun t ht => f.canonical t ⟨ht.1.le, ht.2.le⟩)).mpr
      (f.smoothSection a).contDiffOn_interior

end MaslovFamily

/-- Native section smoothness in the independently constructed vertical
bundle on one parameter–spatial chart. This is actual `ContMDiff`, not a
field asserting agreement with the tensor encoding. -/
def IsSmoothNativeParameterChartSection {n : ℕ}
    (M : SmoothManifold (2 * n)) (J : ℝ → AlmostComplexField M)
    (s : ℝ → M.Point → SquaredCanonicalTensor n)
    (a : M.Point) (A : TopologicalSpace.Opens ℝ)
    (hJ : ContDiffOn ℝ ∞ (fun p => almostComplexInChart M a (J p.1) p.2)
      (parameterSpatialChartDomain M a A : Set (ℝ × Model (2 * n))))
    (hJsq : ∀ t ∈ A, ∀ x v, J t x (J t x v) = -v)
    (hcanonical : ∀ t ∈ A, ∀ x, IsSquaredCanonicalTensor (J t x) (s t x)) : Prop :=
  let hK := parameterChartComplexStructure_smooth M J a A hJ
  let hKsq := parameterChartComplexStructure_sq M J a A hJsq
  let b := verticalCanonicalTensorSquareVectorPrebundle hK hKsq
  letI := b.totalSpaceTopology
  letI := b.toFiberBundle
  ContMDiff 𝓘(ℝ, ℝ × Model (2 * n))
    ((𝓘(ℝ, ℝ × Model (2 * n))).prod 𝓘(ℝ, ℂ)) ∞
    (fun p => (⟨p, parameterChartTensorSquareSection M J s a A hJsq hcanonical p⟩ :
      TotalSpace ℂ (fun p : parameterSpatialChartDomain M a A =>
        CanonicalTensorSquare (parameterChartComplexStructure M J a A p))))

/-- An intrinsic tensor-square section together with native smoothness
on whole-time spatial charts. The complex structure extends to all real
times; compatibility is required only on the parameter interval. This
has its globally glued native total-space atlas and section correspondence
in `IntrinsicVerticalCanonicalBundle`. -/
structure NativeChartedMaslovFamily {n : ℕ} (M : SmoothManifold (2 * n))
    (eta : ℝ → M.Form 2) where
  J : ℝ → AlmostComplexField M
  complex : ∀ t x v, J t x (J t x v) = -v
  compatible : ∀ t ∈ parameterInterval, IsCompatibleAlmostComplex M (eta t) (J t)
  smoothJ : ∀ a, ContDiffOn ℝ ∞
    (fun p => almostComplexInChart M a (J p.1) p.2)
      (parameterSpatialChartDomain M a ⊤ : Set (ℝ × Model (2 * n)))
  tensorSection : ∀ t x, CanonicalTensorSquare (J t x)
  nowhereZero : ∀ t ∈ parameterInterval, ∀ x, tensorSection t x ≠ 0
  smoothSection : ∀ a, IsSmoothNativeParameterChartSection M J
    (fun t x => (canonicalSquareMap (J t x) (tensorSection t x)).val) a ⊤
      (smoothJ a) (fun t _ => complex t)
      (fun t _ x => (canonicalSquareMap (J t x) (tensorSection t x)).property)

namespace NativeChartedMaslovFamily

variable {n : ℕ} {M : SmoothManifold (2 * n)} {eta : ℝ → M.Form 2}

def squaredTensor (f : NativeChartedMaslovFamily M eta)
    (t : ℝ) (x : M.Point) : SquaredCanonicalTensor n :=
  (canonicalSquareMap (f.J t x) (f.tensorSection t x)).val

theorem smooth_squaredTensor (f : NativeChartedMaslovFamily M eta) (a : M.Point) :
    ContDiffOn ℝ ∞ (fun p => squaredTensorInChart M a (f.squaredTensor p.1) p.2)
      (parameterSpatialChartDomain M a ⊤ : Set (ℝ × Model (2 * n))) :=
  (parameterChartTensorSquareSection_smooth_iff M f.J f.squaredTensor a ⊤
    (f.smoothJ a) (fun t _ => f.complex t)
    (fun t _ x => (canonicalSquareMap (f.J t x) (f.tensorSection t x)).property)).mp
      (f.smoothSection a)

/-- Native chart section smoothness produces the encoded joint tensor
regularity by the proved correspondence. No encoded smoothness is input. -/
def toMaslovFamily (f : NativeChartedMaslovFamily M eta) : MaslovFamily M eta where
  J := f.J
  tensor := f.squaredTensor
  compatible := f.compatible
  canonical := fun t _ x => (canonicalSquareMap (f.J t x) (f.tensorSection t x)).property
  nowhereZero := by
    intro t ht x hz
    apply f.nowhereZero t ht x
    apply (canonicalSquareMap_bijective (f.J t x) (f.complex t x)).1
    apply Subtype.ext
    simpa only [squaredTensor, map_zero, Submodule.coe_zero] using hz
  smoothJ := fun a => ⟨(parameterSpatialChartDomain M a ⊤ : Set (ℝ × Model (2 * n))),
    (parameterSpatialChartDomain M a ⊤).isOpen,
    fun p hp => ⟨mem_univ _, hp.2⟩, f.smoothJ a⟩
  smoothSection := fun a =>
    ⟨(parameterSpatialChartDomain M a ⊤ : Set (ℝ × Model (2 * n))),
      (parameterSpatialChartDomain M a ⊤).isOpen,
      fun p hp => ⟨mem_univ _, hp.2⟩, f.smooth_squaredTensor a⟩

/-- The native family supplies a concrete encoded Maslov homotopy with
the same complex structures and natural tensor images at both endpoints. -/
def toMaslovHomotopy {eta : M.Form 2}
    (f : NativeChartedMaslovFamily M (fun _ => eta))
    (s₀ s₁ : MaslovRepresentative M eta)
    (hJ₀ : f.J 0 = s₀.J) (hJ₁ : f.J 1 = s₁.J)
    (hs₀ : f.squaredTensor 0 = s₀.tensor) (hs₁ : f.squaredTensor 1 = s₁.tensor) :
    MaslovHomotopy s₀ s₁ where
  family := f.toMaslovFamily
  sourceJ := hJ₀
  targetJ := hJ₁
  sourceSection := hs₀
  targetSection := hs₁

end NativeChartedMaslovFamily

namespace MaslovFamily

variable {n : ℕ} {M : SmoothManifold (2 * n)} {eta : ℝ → M.Form 2}

/-- Reparametrization changes the ambient two-form, complex structure and
section by the same smooth map. It preserves both endpoints and gives
whole-time complex structures; it is not a lift on the unmodified
varying-form deformation. -/
def nativeReparametrized (f : MaslovFamily M eta) :
    NativeChartedMaslovFamily M (fun t => eta (Real.smoothTransition t)) where
  J := fun t => f.J (Real.smoothTransition t)
  complex := fun t => (f.compatible (Real.smoothTransition t)
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩).2.1
  compatible := fun t _ => f.compatible (Real.smoothTransition t)
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  smoothJ := fun a => (f.smoothJ a).contDiffOn_smoothTransition
  tensorSection := fun t x => (canonicalSquareEquivOfComplexStructure
    (f.J (Real.smoothTransition t) x)
    ((f.compatible (Real.smoothTransition t)
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩).2.1 x)).symm
        ⟨f.tensor (Real.smoothTransition t) x,
          f.canonical (Real.smoothTransition t)
            ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ x⟩
  nowhereZero := by
    intro t _ x hz
    have hh := (canonicalSquareEquivOfComplexStructure
      (f.J (Real.smoothTransition t) x)
      ((f.compatible (Real.smoothTransition t)
        ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩).2.1 x)).apply_symm_apply
          ⟨f.tensor (Real.smoothTransition t) x,
            f.canonical (Real.smoothTransition t)
              ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ x⟩
    rw [hz, map_zero] at hh
    exact f.nowhereZero (Real.smoothTransition t)
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ x
        (congrArg Subtype.val hh).symm
  smoothSection := by
    intro a
    apply (parameterChartTensorSquareSection_smooth_iff
      (hJ := (f.smoothJ a).contDiffOn_smoothTransition) _ _ _ _ _ _ _).mpr
    have he : ∀ t x, (canonicalSquareMap (f.J (Real.smoothTransition t) x)
      ((canonicalSquareEquivOfComplexStructure _
        ((f.compatible (Real.smoothTransition t)
          ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩).2.1 x)).symm
            ⟨f.tensor (Real.smoothTransition t) x,
              f.canonical (Real.smoothTransition t)
                ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ x⟩)).val =
        f.tensor (Real.smoothTransition t) x := by
      intro t x
      exact congrArg Subtype.val ((canonicalSquareEquivOfComplexStructure _
        ((f.compatible (Real.smoothTransition t)
          ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩).2.1 x)).apply_symm_apply _)
    simp_rw [he]
    exact (f.smoothSection a).contDiffOn_smoothTransition

@[simp] theorem nativeReparametrized_squaredTensor (f : MaslovFamily M eta)
    (t : ℝ) (x : M.Point) :
    f.nativeReparametrized.squaredTensor t x = f.tensor (Real.smoothTransition t) x :=
  congrArg Subtype.val ((canonicalSquareEquivOfComplexStructure _
    ((f.compatible (Real.smoothTransition t)
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩).2.1 x)).apply_symm_apply _)

end MaslovFamily

/-- Encoded section homotopies exist exactly when there is an intrinsic
tensor-square section smooth in the constructed native parameter–spatial
charts with the prescribed endpoints. The forward construction uses one
explicit smooth endpoint-preserving time change. This theorem concerns
fixed ambient two-form homotopies, not prescribed pair deformations. -/
theorem maslovHomotopic_iff_nativeChartedFamily {n : ℕ}
    {M : SmoothManifold (2 * n)} {eta : M.Form 2}
    (s₀ s₁ : MaslovRepresentative M eta) :
    MaslovHomotopic s₀ s₁ ↔
      ∃ f : NativeChartedMaslovFamily M (fun _ => eta),
        f.J 0 = s₀.J ∧ f.J 1 = s₁.J ∧
          f.squaredTensor 0 = s₀.tensor ∧ f.squaredTensor 1 = s₁.tensor := by
  constructor
  · rintro ⟨h⟩
    refine ⟨h.family.nativeReparametrized, ?_, ?_, ?_, ?_⟩
    · simpa only [MaslovFamily.nativeReparametrized, Real.smoothTransition.zero]
        using h.sourceJ
    · simpa only [MaslovFamily.nativeReparametrized, Real.smoothTransition.one]
        using h.targetJ
    · funext x
      simpa only [MaslovFamily.nativeReparametrized_squaredTensor,
        Real.smoothTransition.zero] using congrFun h.sourceSection x
    · funext x
      simpa only [MaslovFamily.nativeReparametrized_squaredTensor,
        Real.smoothTransition.one] using congrFun h.targetSection x
  · rintro ⟨f, hJ₀, hJ₁, hs₀, hs₁⟩
    exact ⟨f.toMaslovHomotopy s₀ s₁ hJ₀ hJ₁ hs₀ hs₁⟩

end FsFltz.Geometry
