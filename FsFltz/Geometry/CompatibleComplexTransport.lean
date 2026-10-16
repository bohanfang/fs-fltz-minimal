import FsFltz.Geometry.CanonicalSquareBundle
import FsFltz.Geometry.MaslovHomotopy
import FsFltz.Geometry.BoundaryContactDistribution

/-!
# Explicit transport through compatible complex structures

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244;
`thm:target` / `g:chain`, lines 407–413; `sec:lean`, lines 794–814.
For two structures compatible with the same form, the normalized map
`(id - J₀ ∘ J₁)/2` intertwines `J₁` with `J₀` and is invertible by
positivity. It therefore transports actual nonzero canonical tensors.

The constructions below do not assert existence or contractibility of
compatible paths, or identify the canonical bundle of an odd-dimensional
parameter product with its vertical canonical line.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry

/-- A normalized intertwiner, equal to the identity when the two structures agree. -/
def compatibleComplexTransport {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (J₀ J₁ : E →L[ℝ] E) : E →L[ℝ] E :=
  (2 : ℝ)⁻¹ • (ContinuousLinearMap.id ℝ E - J₀.comp J₁)

theorem compatibleComplexTransport_intertwines {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (J₀ J₁ : E →L[ℝ] E)
    (h₀ : ∀ v, J₀ (J₀ v) = -v) (h₁ : ∀ v, J₁ (J₁ v) = -v) (v : E) :
    compatibleComplexTransport J₀ J₁ (J₁ v) =
      J₀ (compatibleComplexTransport J₀ J₁ v) := by
  simp only [compatibleComplexTransport, smul_apply,
    sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, h₀, h₁, map_neg, map_smul, map_sub]
  module

theorem compatibleComplexTransport_self {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (J : E →L[ℝ] E)
    (hJ : ∀ v, J (J v) = -v) :
    compatibleComplexTransport J J = ContinuousLinearMap.id ℝ E := by
  ext v
  simp only [compatibleComplexTransport, smul_apply,
    sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, hJ]
  module

set_option backward.isDefEq.respectTransparency false in
/-- Common symplectic positivity rules out a kernel. No closeness of the
two compatible structures is required. -/
theorem compatibleComplexTransport_isInvertible {n : ℕ}
    (M : SmoothManifold (2 * n)) (eta : M.Form 2) (J₀ J₁ : AlmostComplexField M)
    (h₀ : IsCompatibleAlmostComplex M eta J₀)
    (h₁ : IsCompatibleAlmostComplex M eta J₁) (x : M.Point) :
    (compatibleComplexTransport (E := Model (2 * n)) (J₀ x) (J₁ x)).IsInvertible := by
  let K₀ : Model (2 * n) →L[ℝ] Model (2 * n) := J₀ x
  let K₁ : Model (2 * n) →L[ℝ] Model (2 * n) := J₁ x
  let A : Model (2 * n) →L[ℝ] Model (2 * n) :=
    compatibleComplexTransport K₀ K₁
  have hker : A.toLinearMap.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    change A v = 0 at hv
    by_contra hne
    have he : v - K₀ (K₁ v) = 0 := by
      have hh : (2 : ℝ) • A v = 0 := by rw [hv, smul_zero]
      simpa [A, compatibleComplexTransport, smul_smul] using hh
    have he' : v = K₀ (K₁ v) := sub_eq_zero.mp he
    have hneg : K₀ v = -K₁ v := by
      calc K₀ v = K₀ (K₀ (K₁ v)) := congrArg K₀ he'
           _ = -K₁ v := h₀.2.1 _ _
    have hp₀ := h₀.2.2.2 x v hne
    have hp₁ := h₁.2.2.2 x v hne
    change J₀ x v = -J₁ x v at hneg
    rw [hneg] at hp₀
    have hn : SmoothManifold.evalTwo eta x v (-J₁ x v) =
        -SmoothManifold.evalTwo eta x v (J₁ x v) := by
      simpa only [neg_one_smul, neg_one_mul] using
        SmoothManifold.evalTwo_smul_right eta x (-1) v (J₁ x v)
    rw [hn] at hp₀
    linarith
  have hinj : Function.Injective A := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective A := LinearMap.injective_iff_surjective.mp hinj
  change A.IsInvertible
  exact ⟨ContinuousLinearEquiv.ofBijective A hker
    (LinearMap.range_eq_top.mpr hsurj), ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- Transport an actual canonical square in all its tangent slots. -/
def transportSquaredTensor {n : ℕ}
    (J₀ J₁ : Model (2 * n) →L[ℝ] Model (2 * n))
    (s : SquaredCanonicalTensor n) : SquaredCanonicalTensor n :=
  s.compContinuousLinearMap (fun _ => compatibleComplexTransport J₀ J₁)

theorem transportSquaredTensor_canonical {n : ℕ}
    (J₀ J₁ : Model (2 * n) →L[ℝ] Model (2 * n))
    (h₀ : ∀ v, J₀ (J₀ v) = -v) (h₁ : ∀ v, J₁ (J₁ v) = -v)
    (s : SquaredCanonicalTensor n) (hs : IsSquaredCanonicalTensor J₀ s) :
    IsSquaredCanonicalTensor J₁ (transportSquaredTensor J₀ J₁ s) :=
  isSquaredCanonicalTensor_comp_of_intertwines _ _ _
    (compatibleComplexTransport_intertwines J₀ J₁ h₀ h₁) s hs

theorem transportSquaredTensor_ne_zero {n : ℕ}
    (J₀ J₁ : Model (2 * n) →L[ℝ] Model (2 * n))
    (hinv : (compatibleComplexTransport J₀ J₁).IsInvertible)
    (s : SquaredCanonicalTensor n) (hs : s ≠ 0) :
    transportSquaredTensor J₀ J₁ s ≠ 0 := by
  intro hz
  apply hs
  ext v
  have he := congrArg (fun t : SquaredCanonicalTensor n =>
    t (fun i => (compatibleComplexTransport J₀ J₁).inverse (v i))) hz
  simpa [transportSquaredTensor, hinv.self_apply_inverse] using he

@[simp] theorem transportSquaredTensor_self {n : ℕ}
    (J : Model (2 * n) →L[ℝ] Model (2 * n)) (hJ : ∀ v, J (J v) = -v)
    (s : SquaredCanonicalTensor n) : transportSquaredTensor J J s = s := by
  ext v
  simp [transportSquaredTensor, compatibleComplexTransport_self J hJ]

set_option backward.isDefEq.respectTransparency false in
/-- The actual inverse chart derivative intertwines the normalized transport.
Both sides use the same vertical tangent variables. -/
theorem inverseChartTangentMap_compatibleComplexTransport {n : ℕ}
    (M : SmoothManifold (2 * n)) (a : M.Point) (J₀ J₁ : AlmostComplexField M)
    (y : Model (2 * n)) (hy : y ∈ (chartAt (Model (2 * n)) a).target)
    (v : Model (2 * n)) :
    M.inverseChartTangentMap a y
      (compatibleComplexTransport (almostComplexInChart M a J₀ y)
        (almostComplexInChart M a J₁ y) v) =
      compatibleComplexTransport (J₀ ((chartAt (Model (2 * n)) a).symm y))
        (J₁ ((chartAt (Model (2 * n)) a).symm y)) (M.inverseChartTangentMap a y v) := by
  simp only [compatibleComplexTransport, smul_apply, sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, map_smul, map_sub]
  rw [inverseChartTangentMap_almostComplexInChart M a J₀ y hy,
    inverseChartTangentMap_almostComplexInChart M a J₁ y hy]

set_option backward.isDefEq.respectTransparency false in
/-- Transport in a chart is exactly transport by the chart expressions of
the two structures, proved using the actual inverse chart differential. -/
theorem squaredTensorInChart_transport {n : ℕ} (M : SmoothManifold (2 * n))
    (a : M.Point) (J₀ J₁ : AlmostComplexField M)
    (s : M.Point → SquaredCanonicalTensor n) (y : Model (2 * n))
    (hy : y ∈ (chartAt (Model (2 * n)) a).target) :
    squaredTensorInChart M a (fun x => transportSquaredTensor (J₀ x) (J₁ x) (s x)) y =
      transportSquaredTensor (almostComplexInChart M a J₀ y)
        (almostComplexInChart M a J₁ y) (squaredTensorInChart M a s y) := by
  ext v
  apply congrArg (s ((chartAt (Model (2 * n)) a).symm y))
  funext i
  exact (inverseChartTangentMap_compatibleComplexTransport M a J₀ J₁ y hy (v i)).symm

/-- Smooth transport is polynomial in the structures and multilinear in
the tensor, so it also works for varying source tensors and parameters. -/
theorem contDiffOn_transportSquaredTensor {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}
    {J₀ J₁ : E → Model (2 * n) →L[ℝ] Model (2 * n)}
    {s : E → SquaredCanonicalTensor n}
    (h₀ : ContDiffOn ℝ ∞ J₀ U) (h₁ : ContDiffOn ℝ ∞ J₁ U)
    (hs : ContDiffOn ℝ ∞ s U) :
    ContDiffOn ℝ ∞ (fun x => transportSquaredTensor (J₀ x) (J₁ x) (s x)) U := by
  have hA : ContDiffOn ℝ ∞ (fun x => compatibleComplexTransport (J₀ x) (J₁ x)) U :=
    ((contDiffOn_const (c := ContinuousLinearMap.id ℝ (Model (2 * n)))).sub
      (h₀.clm_comp h₁)).const_smul _
  let C := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin n ⊕ Fin n => Model (2 * n))
    (fun _ : Fin n ⊕ Fin n => Model (2 * n)) ℂ
  have hC : ContDiff ℝ ∞ (fun L => C L) :=
    ContinuousMultilinearMap.contDiff (𝕜 := ℝ)
      (F := SquaredCanonicalTensor n →L[ℝ] SquaredCanonicalTensor n) C
  exact (hC.comp_contDiffOn (contDiffOn_pi.mpr (fun _ => hA))).clm_apply hs

namespace SmoothNearInterval

/-- Transport preserves joint smoothness on a genuine open neighborhood
of the interval, with no uniform time collar assumption. -/
theorem transportSquaredTensor {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Set E}
    {J₀ J₁ : ℝ × E → Model (2 * n) →L[ℝ] Model (2 * n)}
    {s : ℝ × E → SquaredCanonicalTensor n}
    (h₀ : SmoothNearInterval V J₀) (h₁ : SmoothNearInterval V J₁)
    (hs : SmoothNearInterval V s) :
    SmoothNearInterval V (fun p =>
      FsFltz.Geometry.transportSquaredTensor (J₀ p) (J₁ p) (s p)) := by
  obtain ⟨U₀, ho₀, hi₀, hd₀⟩ := h₀
  obtain ⟨U₁, ho₁, hi₁, hd₁⟩ := h₁
  obtain ⟨U₂, ho₂, hi₂, hd₂⟩ := hs
  refine ⟨(U₀ ∩ U₁) ∩ U₂, (ho₀.inter ho₁).inter ho₂,
    fun p hp => ⟨⟨hi₀ hp, hi₁ hp⟩, hi₂ hp⟩, ?_⟩
  exact contDiffOn_transportSquaredTensor
    (hd₀.mono (fun _ hp => hp.1.1))
    (hd₁.mono (fun _ hp => hp.1.2)) (hd₂.mono inter_subset_right)

end SmoothNearInterval

set_option backward.isDefEq.respectTransparency false in
theorem isSmoothSquaredTensorSection_transport {n : ℕ}
    (M : SmoothManifold (2 * n)) (J₀ J₁ : AlmostComplexField M)
    (h₀ : IsSmoothAlmostComplexField M J₀) (h₁ : IsSmoothAlmostComplexField M J₁)
    (s : M.Point → SquaredCanonicalTensor n) (hs : IsSmoothSquaredTensorSection M s) :
    IsSmoothSquaredTensorSection M
      (fun x => transportSquaredTensor (J₀ x) (J₁ x) (s x)) := by
  intro a
  exact (contDiffOn_transportSquaredTensor (h₀ a) (h₁ a) (hs a)).congr
    (fun y hy => squaredTensorInChart_transport M a J₀ J₁ s y hy)

namespace MaslovRepresentative

set_option backward.isDefEq.respectTransparency false in
/-- Change the compatible structure and construct the transported actual
section; neither its smoothness nor its nonvanishing is supplied. -/
def changeCompatibleStructure {n : ℕ} {M : SmoothManifold (2 * n)} {eta : M.Form 2}
    (s : MaslovRepresentative M eta) (J : AlmostComplexField M)
    (hJ : IsCompatibleAlmostComplex M eta J) : MaslovRepresentative M eta where
  J := J
  compatible := hJ
  tensor := fun x => transportSquaredTensor (s.J x) (J x) (s.tensor x)
  canonical := fun x => transportSquaredTensor_canonical _ _
    (s.compatible.2.1 x) (hJ.2.1 x) _ (s.canonical x)
  smooth := isSmoothSquaredTensorSection_transport M s.J J s.compatible.1 hJ.1
    s.tensor s.smooth
  nowhereZero := fun x => transportSquaredTensor_ne_zero _ _
    (compatibleComplexTransport_isInvertible M eta s.J J s.compatible hJ x)
    _ (s.nowhereZero x)

set_option backward.isDefEq.respectTransparency false in
/-- The constructed transport is an actual native smooth tensor-square
section in the independently built bundle for the new structure. -/
theorem contMDiff_changeCompatibleStructure_tensorSquareSection {n : ℕ}
    {M : SmoothManifold (2 * n)} {eta : M.Form 2} (s : MaslovRepresentative M eta)
    (J : AlmostComplexField M) (hJ : IsCompatibleAlmostComplex M eta J) :
    let a := canonicalTensorSquareVectorPrebundle M J hJ.1 hJ.2.1
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    ContMDiff 𝓘(ℝ, Model (2 * n)) ((𝓘(ℝ, Model (2 * n))).prod 𝓘(ℝ, ℂ)) ∞
      (fun x => (⟨x, (s.changeCompatibleStructure J hJ).canonicalTensorSquareSection x⟩ :
        Bundle.TotalSpace ℂ (fun x : M.Point => CanonicalTensorSquare (J x)))) :=
  (s.changeCompatibleStructure J hJ).contMDiff_canonicalTensorSquareBundleSection

end MaslovRepresentative

set_option backward.isDefEq.respectTransparency false in
/-- Joint smoothness of transport in the actual spatial chart. The open
neighborhood is intersected with that chart, so no off-chart equality is used. -/
theorem smoothNearInterval_squaredTensor_transport {n : ℕ}
    (M : SmoothManifold (2 * n)) (J₀ J₁ : ℝ → AlmostComplexField M)
    (s : ℝ → M.Point → SquaredCanonicalTensor n) (a : M.Point)
    (h₀ : SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun p => almostComplexInChart M a (J₀ p.1) p.2))
    (h₁ : SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun p => almostComplexInChart M a (J₁ p.1) p.2))
    (hs : SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun p => squaredTensorInChart M a (s p.1) p.2)) :
    SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun p => squaredTensorInChart M a
        (fun x => transportSquaredTensor (J₀ p.1 x) (J₁ p.1 x) (s p.1 x)) p.2) := by
  obtain ⟨U, hU, hi, hd⟩ := h₀.transportSquaredTensor h₁ hs
  let V : Set (ℝ × Model (2 * n)) := univ ×ˢ (chartAt (Model (2 * n)) a).target
  refine ⟨U ∩ V, hU.inter (isOpen_univ.prod (chartAt (Model (2 * n)) a).open_target),
    fun p hp => ⟨hi hp, mem_univ _, hp.2⟩, ?_⟩
  exact (hd.mono inter_subset_left).congr (fun p hp =>
    squaredTensorInChart_transport M a (J₀ p.1) (J₁ p.1) (s p.1) p.2 hp.2.2)

namespace MaslovFamily

set_option backward.isDefEq.respectTransparency false in
/-- Transport even a varying source tensor to a second compatible structure
family. Positivity is relative to the same form at each parameter value. -/
def changeCompatibleStructure {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : ℝ → M.Form 2} (s : MaslovFamily M eta) (J : ℝ → AlmostComplexField M)
    (hJ : ∀ t ∈ parameterInterval, IsCompatibleAlmostComplex M (eta t) (J t))
    (hsmooth : ∀ a, SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun p => almostComplexInChart M a (J p.1) p.2)) : MaslovFamily M eta where
  J := J
  tensor := fun t x => transportSquaredTensor (s.J t x) (J t x) (s.tensor t x)
  compatible := hJ
  canonical := fun t ht x => transportSquaredTensor_canonical _ _
    ((s.compatible t ht).2.1 x) ((hJ t ht).2.1 x) _ (s.canonical t ht x)
  nowhereZero := fun t ht x => transportSquaredTensor_ne_zero _ _
    (compatibleComplexTransport_isInvertible M (eta t) (s.J t) (J t)
      (s.compatible t ht) (hJ t ht) x) _ (s.nowhereZero t ht x)
  smoothJ := hsmooth
  smoothSection := fun a => smoothNearInterval_squaredTensor_transport M s.J J s.tensor a
    (s.smoothJ a) (hsmooth a) (s.smoothSection a)

end MaslovFamily

namespace MaslovRepresentative

set_option backward.isDefEq.respectTransparency false in
/-- Construct the actual nonvanishing section family from a compatible
complex-structure path and one initial representative. No section family
or endpoint transported tensor is an input. -/
def familyChangeCompatibleStructure {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : M.Form 2} (s : MaslovRepresentative M eta) (J : ℝ → AlmostComplexField M)
    (hJ : ∀ t ∈ parameterInterval, IsCompatibleAlmostComplex M eta (J t))
    (hsmooth : ∀ a, SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun p => almostComplexInChart M a (J p.1) p.2)) :
    MaslovFamily M (fun _ => eta) :=
  (MaslovHomotopy.refl s).family.changeCompatibleStructure J hJ hsmooth

set_option backward.isDefEq.respectTransparency false in
/-- The constructed family is a concrete Maslov homotopy from the initial
representative to precisely its transported endpoint representative. -/
def homotopyChangeCompatibleStructure {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : M.Form 2} (s : MaslovRepresentative M eta) (J : ℝ → AlmostComplexField M)
    (hJ : ∀ t ∈ parameterInterval, IsCompatibleAlmostComplex M eta (J t))
    (hsmooth : ∀ a, SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun p => almostComplexInChart M a (J p.1) p.2)) (hsource : J 0 = s.J) :
    MaslovHomotopy s (s.changeCompatibleStructure (J 1) (hJ 1 parameterOne.property)) where
  family := s.familyChangeCompatibleStructure J hJ hsmooth
  sourceJ := hsource
  targetJ := rfl
  sourceSection := by
    change (fun x => transportSquaredTensor (s.J x) (J 0 x) (s.tensor x)) = s.tensor
    rw [hsource]
    funext x
    exact transportSquaredTensor_self _ (s.compatible.2.1 x) _
  targetSection := rfl

/-- Existing concrete quotient equality now consumes the constructed section
homotopy; a compatible path alone suffices for this prescribed endpoint. -/
theorem class_eq_changeCompatibleStructure {n : ℕ} {M : SmoothManifold (2 * n)}
    {eta : M.Form 2} (s : MaslovRepresentative M eta) (J : ℝ → AlmostComplexField M)
    (hJ : ∀ t ∈ parameterInterval, IsCompatibleAlmostComplex M eta (J t))
    (hsmooth : ∀ a, SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun p => almostComplexInChart M a (J p.1) p.2)) (hsource : J 0 = s.J) :
    (Quot.mk _ s : MaslovClass M eta) =
      Quot.mk _ (s.changeCompatibleStructure (J 1) (hJ 1 parameterOne.property)) :=
  Quot.sound ⟨s.homotopyChangeCompatibleStructure J hJ hsmooth hsource⟩

end MaslovRepresentative

namespace MaslovHomotopy

set_option backward.isDefEq.respectTransparency false in
/-- Normalize an arbitrary existing varying-structure homotopy to one fixed
compatible structure. Its section is transported jointly in time and space,
and its endpoints are the transported original representatives. -/
def changeCompatibleStructure {n : ℕ} {M : SmoothManifold (2 * n)} {eta : M.Form 2}
    {s₀ s₁ : MaslovRepresentative M eta} (h : MaslovHomotopy s₀ s₁)
    (J : AlmostComplexField M) (hJ : IsCompatibleAlmostComplex M eta J) :
    MaslovHomotopy (s₀.changeCompatibleStructure J hJ)
      (s₁.changeCompatibleStructure J hJ) where
  family := h.family.changeCompatibleStructure (fun _ => J) (fun _ _ => hJ)
    (fun a => SmoothNearInterval.constant (chartAt (Model (2 * n)) a).open_target (hJ.1 a))
  sourceJ := rfl
  targetJ := rfl
  sourceSection := by
    change (fun x => transportSquaredTensor (h.family.J 0 x) (J x)
      (h.family.tensor 0 x)) = _
    rw [h.sourceJ, h.sourceSection]
    rfl
  targetSection := by
    change (fun x => transportSquaredTensor (h.family.J 1 x) (J x)
      (h.family.tensor 1 x)) = _
    rw [h.targetJ, h.targetSection]
    rfl

end MaslovHomotopy

end FsFltz.Geometry
