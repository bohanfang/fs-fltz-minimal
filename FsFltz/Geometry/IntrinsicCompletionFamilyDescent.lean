import FsFltz.Geometry.IntrinsicCompletionFamilyCharts

/-!
# Descent through the original completion attachment

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158;
`def:chain`, lines 163–199; and `sec:lean`, lines 788–814.
Maps on the actual native carrier and full cylinder descend uniquely when
they agree on the original half collar. The parameter version keeps the
original shared quotient and its topology. Smoothness and invertibility
are separate obligations.
-/

noncomputable section
open Set Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

section General

variable {M B X : Type*} [TopologicalSpace M] [TopologicalSpace B]
  [TopologicalSpace X] {δ : ℝ} (C : Half δ B → M)
  (f : M → X) (g : Band δ B → X)
  (hseam : ∀ p, f (C p) = g (halfToBand p))

/-- The literal quotient descent, using the native representative on the seam. -/
def descendMap (x : Space C) : X :=
  Sum.elim f (fun p => g p.val) (normalEquiv C x)

omit [TopologicalSpace M] [TopologicalSpace B] [TopologicalSpace X] in
@[simp] theorem descendMap_original (x : M) :
    descendMap C f g (original C x) = f x := rfl

include hseam in
omit [TopologicalSpace M] [TopologicalSpace B] [TopologicalSpace X] in
@[simp] theorem descendMap_cylinder (p : Band δ B) :
    descendMap C f g (cylinder C p) = g p := by
  change Sum.elim f (fun q => g q.val) (normalize C (.inr p)) = g p
  by_cases hp : 0 ≤ p.val.1
  · simp only [normalize, hp, ↓reduceDIte, Sum.elim_inl]
    exact hseam (halfOfNonneg p hp)
  · simp only [normalize, hp, ↓reduceDIte, Sum.elim_inr]

include hseam in
/-- Continuity descends for the actual attachment quotient topology. -/
theorem continuous_descendMap (hf : Continuous f) (hg : Continuous g) :
    Continuous (descendMap C f g) := by
  apply (isQuotientMap_quotient_mk' (s := Setoid.ker (normalize C))).continuous_iff.mpr
  apply continuous_sum_dom.mpr
  constructor
  · exact hf
  · change Continuous (fun p => descendMap C f g (cylinder C p))
    simpa only [descendMap_cylinder C f g hseam] using hg

omit [TopologicalSpace M] [TopologicalSpace B] [TopologicalSpace X] in
/-- The two original inclusions determine the descended map uniquely. -/
theorem descendMap_unique (q : Space C → X)
    (hf : ∀ x, q (original C x) = f x)
    (hg : ∀ p, q (cylinder C p) = g p) : q = descendMap C f g := by
  have hs : ∀ p, f (C p) = g (halfToBand p) := by
    intro p
    rw [← hf, original_collar_eq_cylinder, hg]
  funext x
  rcases jointly_surjective C x with ⟨y, rfl⟩ | ⟨p, rfl⟩
  · exact hf y
  · rw [descendMap_cylinder C f g hs]
    exact hg p

end General

section Family

variable {T M B X : Type*} [TopologicalSpace T] [TopologicalSpace M]
  [TopologicalSpace B] [TopologicalSpace X] {δ : ℝ}
  (C : T → Half δ B → M) (f : T × M → X) (g : T × Band δ B → X)
  (hseam : ∀ t p, f (t, C t p) = g (t, halfToBand p))

/-- Native and cylinder maps with their actual parameter descend through
the original varying attachment. -/
def totalDescendMap : TotalSpace C → X :=
  descendMap (totalCollar C) f (g ∘ parameterBandHomeomorph.symm)

include hseam in
omit [TopologicalSpace M] [TopologicalSpace X] in
private theorem totalDescendMap_seam (p : Half δ (T × B)) :
    f (totalCollar C p) =
      (g ∘ parameterBandHomeomorph.symm) (halfToBand p) :=
  hseam p.val.2.1 ⟨(p.val.1, p.val.2.2), p.property.1, mem_univ _⟩

omit [TopologicalSpace M] [TopologicalSpace X] in
@[simp] theorem totalDescendMap_original (t : T) (x : M) :
    totalDescendMap C f g (original (totalCollar C) (t, x)) = f (t, x) := rfl

include hseam in
omit [TopologicalSpace M] [TopologicalSpace X] in
@[simp] theorem totalDescendMap_cylinder (p : T × Band δ B) :
    totalDescendMap C f g (totalCylinder C p) = g p := by
  rw [totalDescendMap, totalCylinder,
    descendMap_cylinder _ _ _ (totalDescendMap_seam C f g hseam)]
  exact congrArg g (parameterBandHomeomorph.symm_apply_apply p)

include hseam in
theorem continuous_totalDescendMap (hf : Continuous f) (hg : Continuous g) :
    Continuous (totalDescendMap C f g) :=
  continuous_descendMap _ _ _ (totalDescendMap_seam C f g hseam) hf
    (hg.comp parameterBandHomeomorph.symm.continuous)

include hseam in
omit [TopologicalSpace M] [TopologicalSpace X] in
/-- Descent commutes with the original slice inclusion, retaining the exact
native and cylinder formulas at every parameter. -/
theorem totalDescendMap_sliceIn (t : T) (x : Space (C t)) :
    totalDescendMap C f g (sliceIn C t x) =
      descendMap (C t) (fun y => f (t, y)) (fun p => g (t, p)) x := by
  rcases jointly_surjective (C t) x with ⟨y, rfl⟩ | ⟨p, rfl⟩
  · rw [sliceIn_original, totalDescendMap_original, descendMap_original]
  · rw [sliceIn_cylinder, totalDescendMap_cylinder C f g hseam,
      descendMap_cylinder _ _ _ (hseam t)]

include hseam in
/-- A smooth or continuous end formula only needs to cover a positive
inward neighborhood of the seam. The remaining inward cylinder inherits
continuity from the original native collar, without reducing its width. -/
theorem continuous_cylinderMap_of_end_strip (hδ : 0 < δ)
    (hC : Continuous (totalCollar C)) (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε)
    (hg : ContinuousOn g {p | p.2.val.1 < ε}) : Continuous g := by
  let F : T × Band δ B → X :=
    f ∘ totalCollar C ∘ foldBand hδ ∘ parameterBandHomeomorph
  have hF : Continuous F := hf.comp (hC.comp
    ((continuous_foldBand hδ).comp parameterBandHomeomorph.continuous))
  have heq (p : T × Band δ B) (hp : 0 ≤ p.2.val.1) : F p = g p := by
    change f (p.1, C p.1 (foldBand hδ p.2)) = g p
    rw [hseam]
    apply congrArg g
    refine Prod.ext ?_ ?_
    · rfl
    apply Subtype.ext
    exact Prod.ext (max_eq_left hp) rfl
  have hr : Continuous (fun p : T × Band δ B => p.2.val.1) :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p.2.val.1 < ε
  · exact (hg p hp).continuousAt ((isOpen_lt hr continuous_const).mem_nhds hp)
  · have hpos : 0 < p.2.val.1 := lt_of_lt_of_le hε (le_of_not_gt hp)
    apply hF.continuousAt.congr_of_eventuallyEq
    have hn := hr.continuousAt.eventually (Ioi_mem_nhds hpos)
    filter_upwards [hn] with q hq
    exact (heq q (le_of_lt hq)).symm

include hseam in
/-- End-strip continuity and the original collar square suffice for a
continuous map on the entire unmodified shared completion quotient. -/
theorem continuous_totalDescendMap_of_end_strip (hδ : 0 < δ)
    (hC : Continuous (totalCollar C)) (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε)
    (hg : ContinuousOn g {p | p.2.val.1 < ε}) :
    Continuous (totalDescendMap C f g) :=
  continuous_totalDescendMap C f g hseam hf
    (continuous_cylinderMap_of_end_strip C f g hseam hδ hC hf hε hg)

end Family

end FsFltz.Geometry.IntrinsicCompletionGluing
