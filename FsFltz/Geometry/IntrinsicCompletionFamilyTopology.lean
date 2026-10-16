import FsFltz.Geometry.IntrinsicCompletionFamilyCharts
import Mathlib.Topology.LocalAtTarget

/-!
# Topology of the original shared completion quotient

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–814.
The topology throughout is the actual attachment quotient topology.
Hausdorffness and second countability are derived from the original
carrier and the shared open collar. The original slice equivalence becomes
a homeomorphism by the native interior and full cylinder patches.
No total-space topology is transported from a product or a fiber model.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

section General

variable {T M B : Type*} [TopologicalSpace T] [TopologicalSpace M]
  [TopologicalSpace B] {δ : ℝ} (hδ : 0 < δ) (C : T → Half δ B → M)

include hδ in
/-- Hausdorffness of the shared quotient follows from the actual joint collar. -/
theorem t2Space_totalSpace [T2Space T] [T2Space M] [T2Space B]
    (hC : IsOpenEmbedding (totalCollar C)) : T2Space (TotalSpace C) :=
  t2Space_space hδ (totalCollar C) hC

omit [TopologicalSpace M] in
/-- The original slice map is injective, independently of collar regularity. -/
theorem sliceIn_injective (t : T) : Function.Injective (sliceIn C t) := by
  intro x y h
  apply (fiberEquiv C t).injective
  exact Subtype.ext h

end General

section Native

variable {T M : Type*} [TopologicalSpace T] [TopologicalSpace M] {k : ℕ}
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M] [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ) (C : T → Half δ (IntrinsicBoundary.Point k M) → M)
  (hzero : ∀ t b, C t ⟨(0, b), ⟨le_rfl, hδ⟩, mem_univ _⟩ = b.val)
  (hC : IsOpenEmbedding (totalCollar C))

include hδ hzero hC

/-- The two shared open patches prove second countability, including
the empty-boundary case. -/
theorem secondCountableTopology_totalSpace [SecondCountableTopology T]
    [SecondCountableTopology M] : SecondCountableTopology (TotalSpace C) := by
  let U : Bool → Set (TotalSpace C) := fun b =>
    if b then range (totalInterior C) else range (totalCylinder C)
  have hi := isOpenEmbedding_totalInterior hδ C hzero hC
  have hc := isOpenEmbedding_totalCylinder C hC
  have : ∀ b, SecondCountableTopology (U b) := by
    intro b
    cases b with
    | false => exact hc.isEmbedding.toHomeomorph.symm.secondCountableTopology
    | true => exact hi.isEmbedding.toHomeomorph.symm.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := U) ?_ ?_
  · intro b
    cases b with
    | false => exact hc.isOpen_range
    | true => exact hi.isOpen_range
  · ext x
    constructor
    · intro _
      exact mem_univ _
    · intro _
      rcases totalInterior_cylinder_cover hδ C hzero x with ⟨p, hp⟩ | ⟨p, hp⟩
      · exact mem_iUnion.mpr ⟨true, p, hp⟩
      · exact mem_iUnion.mpr ⟨false, p, hp⟩

/-- Each original completion slice carries its actual quotient topology
as a subspace of the actual shared quotient. -/
theorem isEmbedding_sliceIn (t : T) : IsEmbedding (sliceIn C t) := by
  have hi := isOpenEmbedding_totalInterior hδ C hzero hC
  have hc := isOpenEmbedding_totalCylinder C hC
  let U : Bool → TopologicalSpace.Opens (TotalSpace C) := fun b =>
    if b then ⟨range (totalInterior C), hi.isOpen_range⟩
      else ⟨range (totalCylinder C), hc.isOpen_range⟩
  let V : Bool → Type _ := fun b => match b with
    | true => IntrinsicInterior.Point k M
    | false => Band δ (IntrinsicBoundary.Point k M)
  let : (b : Bool) → TopologicalSpace (V b) := fun b => match b with
    | true => inferInstanceAs (TopologicalSpace (IntrinsicInterior.Point k M))
    | false => inferInstanceAs (TopologicalSpace (Band δ (IntrinsicBoundary.Point k M)))
  let iV : (b : Bool) → V b → Space (C t) := fun b =>
    match b with
    | true => interiorIn (C t)
    | false => cylinder (C t)
  apply isEmbedding_of_iSup_eq_top_of_preimage_subset_range (sliceIn C t)
    (continuous_sliceIn C t) U ?_ V iV ?_ ?_ ?_
  · intro x _
    rw [TopologicalSpace.Opens.coe_iSup]
    rcases totalInterior_cylinder_cover hδ C hzero x with ⟨p, hp⟩ | ⟨p, hp⟩
    · exact mem_iUnion.mpr ⟨true, p, hp⟩
    · exact mem_iUnion.mpr ⟨false, p, hp⟩
  · intro b
    cases b with
    | false => exact continuous_cylinder (C t)
    | true => exact (continuous_original (C t)).comp continuous_subtype_val
  · intro b x hx
    cases b with
    | false =>
      obtain ⟨⟨s, p⟩, hp⟩ := hx
      have ht : s = t := by
        have hh := congrArg (parameter C) hp
        simpa only [parameter_totalCylinder, parameter_sliceIn] using hh
      subst s
      exact ⟨p, (sliceIn_injective C t) ((sliceIn_cylinder C t p).trans hp)⟩
    | true =>
      obtain ⟨⟨s, y⟩, hy⟩ := hx
      have ht : s = t := by
        have hh := congrArg (parameter C) hy
        simpa only [totalInterior, parameter_original, parameter_sliceIn] using hh
      subst s
      exact ⟨y, (sliceIn_injective C t) ((sliceIn_original C t y.val).trans hy)⟩
  · intro b
    cases b with
    | false =>
      have he : IsEmbedding (fun p : Band δ (IntrinsicBoundary.Point k M) => (t, p)) :=
        IsEmbedding.of_leftInverse (fun _ => rfl) continuous_snd
          (continuous_const.prodMk continuous_id)
      have hh := hc.isEmbedding.comp he
      simpa only [Function.comp_def, iV, sliceIn_cylinder] using hh
    | true =>
      have he : IsEmbedding (fun y : IntrinsicInterior.Point k M => (t, y)) :=
        IsEmbedding.of_leftInverse (fun _ => rfl) continuous_snd
          (continuous_const.prodMk continuous_id)
      have hh := hi.isEmbedding.comp he
      simpa only [Function.comp_def, iV, interiorIn, sliceIn_original, totalInterior] using hh

/-- The original equivalence of each completion with its parameter fiber
is a homeomorphism for the quotient and subspace topologies. -/
def fiberHomeomorph (t : T) :
    Space (C t) ≃ₜ {x : TotalSpace C // parameter C x = t} where
  toEquiv := fiberEquiv C t
  continuous_toFun := (continuous_sliceIn C t).subtype_mk _
  continuous_invFun := by
    apply (isEmbedding_sliceIn hδ C hzero hC t).continuous_iff.mpr
    have he : sliceIn C t ∘ (fiberEquiv C t).symm = Subtype.val := by
      funext x
      exact congrArg Subtype.val ((fiberEquiv C t).apply_symm_apply x)
    change Continuous (sliceIn C t ∘ (fiberEquiv C t).symm)
    rw [he]
    exact continuous_subtype_val

@[simp] theorem fiberHomeomorph_toEquiv (t : T) :
    (fiberHomeomorph hδ C hzero hC t).toEquiv = fiberEquiv C t := rfl

@[simp] theorem fiberHomeomorph_val (t : T) (x : Space (C t)) :
    (fiberHomeomorph hδ C hzero hC t x).val = sliceIn C t x := rfl

end Native

end FsFltz.Geometry.IntrinsicCompletionGluing
