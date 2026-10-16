import FsFltz.Geometry.CanonicalSquareBundle

/-!
# Pretrivializations from actual fiber coordinates

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–232, and
`sec:lean`, lines 788–814. This construction installs continuous linear
coordinates on an open base set. It does not ask for a section or for
transition regularity; transition regularity is a separate obligation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical Topology
open Set Topology Bundle

namespace FsFltz.Geometry

variable {B : Type*} [TopologicalSpace B] (E : B → Type*)
  [∀ x, AddCommMonoid (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, TopologicalSpace (E x)]

/-- Reindex a fiber along a literal equality of base points. -/
def continuousLinearFiberCast {x y : B} (h : x = y) : E x ≃L[ℂ] E y := by
  cases h
  exact ContinuousLinearEquiv.refl ℂ (E x)

omit [TopologicalSpace B] in
@[simp] theorem continuousLinearFiberCast_rfl (x : B) :
    continuousLinearFiberCast E (rfl : x = x) = ContinuousLinearEquiv.refl ℂ (E x) := rfl

variable {E} (U : Set B) (hU : IsOpen U)
  (e : ∀ x, x ∈ U → E x ≃L[ℂ] ℂ)

/-- A coordinate chart with the literal given fibers and image base set.
Outside its source both fiber formulas are zero. -/
def canonicalPretrivialization : Pretrivialization ℂ (π ℂ E) where
  toFun p := (p.proj, if hp : p.proj ∈ U then e p.proj hp p.snd else 0)
  invFun p := ⟨p.1, if hp : p.1 ∈ U then (e p.1 hp).symm p.2 else 0⟩
  source := (π ℂ E) ⁻¹' U
  target := U ×ˢ univ
  map_source' p hp := ⟨hp, mem_univ _⟩
  map_target' p hp := hp.1
  left_inv' p hp := by
    rcases p with ⟨x, v⟩
    change x ∈ U at hp
    simp only [dite_eq_left hp, ContinuousLinearEquiv.symm_apply_apply]
  right_inv' p hp := by
    simp only [dite_eq_left hp.1, ContinuousLinearEquiv.apply_symm_apply, Prod.mk.eta]
  open_target := hU.prod isOpen_univ
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp] theorem canonicalPretrivialization_apply {x : B} (hx : x ∈ U) (v : E x) :
    canonicalPretrivialization U hU e ⟨x, v⟩ = (x, e x hx v) := by
  change (x, if hp : x ∈ U then e x hp v else 0) = _
  rw [dite_eq_left hx]

instance canonicalPretrivialization_complexLinear :
    (canonicalPretrivialization U hU e).IsLinear ℂ where
  linear x hx := by
    change x ∈ U at hx
    change IsLinearMap ℂ (fun v => if hp : x ∈ U then e x hp v else 0)
    simp only [dite_eq_left hx]
    exact (e x hx).toLinearMap.isLinear

instance canonicalPretrivialization_realLinear
    [∀ x, Module ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)] :
    (canonicalPretrivialization U hU e).IsLinear ℝ where
  linear x hx := by
    change x ∈ U at hx
    change IsLinearMap ℝ (fun v => if hp : x ∈ U then e x hp v else 0)
    simp only [dite_eq_left hx]
    exact ((e x hx).toLinearMap.restrictScalars ℝ).isLinear

theorem canonicalPretrivialization_symm {x : B} (hx : x ∈ U) (q : ℂ) :
    (canonicalPretrivialization U hU e).symm x q = (e x hx).symm q := by
  apply (e x hx).injective
  rw [(e x hx).apply_symm_apply]
  have h := congrArg Prod.snd ((canonicalPretrivialization U hU e).apply_mk_symm hx q)
  simpa only [canonicalPretrivialization_apply U hU e hx] using h

theorem canonicalPretrivialization_isInducing {x : B} (hx : x ∈ U) :
    IsInducing (canonicalPretrivialization U hU e ∘ Bundle.TotalSpace.mk x) := by
  have hc : Continuous (canonicalPretrivialization U hU e ∘ Bundle.TotalSpace.mk x) := by
    simpa only [Function.comp_def, canonicalPretrivialization_apply U hU e hx] using
      continuous_const.prodMk (e x hx).continuous
  have hi : IsInducing (Prod.snd ∘ canonicalPretrivialization U hU e ∘ Bundle.TotalSpace.mk x) := by
    simpa only [Function.comp_def, canonicalPretrivialization_apply U hU e hx,
      ContinuousLinearEquiv.coe_toHomeomorph] using
      (e x hx).toHomeomorph.isInducing
  exact IsInducing.of_comp hc continuous_snd hi

end FsFltz.Geometry

namespace FsFltz.Geometry

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  {E : B → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, TopologicalSpace (E x)]
  {F : A → Type*} [∀ x, AddCommMonoid (F x)] [∀ x, Module ℂ (F x)]
  [∀ x, TopologicalSpace (F x)]
  (i : A → B) (U : Set A)
  (ident : ∀ a, E (i a) ≃L[ℂ] F a)
  (e : ∀ a, a ∈ U → F a ≃L[ℂ] ℂ)

/-- Extend actual branch fiber coordinates to their image in the original
base. The chosen preimage is unique for an embedding; no global inverse
or inhabitedness of the branch is needed. -/
def imageFiberCoordinateEquiv (b : B) (hb : b ∈ i '' U) : E b ≃L[ℂ] ℂ :=
  ((continuousLinearFiberCast E hb.choose_spec.2.symm).trans
    (ident hb.choose)).trans (e hb.choose hb.choose_spec.1)

include i in
omit [TopologicalSpace A] [TopologicalSpace B] in
theorem imageFiberCoordinateEquiv_apply (hi : Function.Injective i)
    (a : A) (ha : a ∈ U) (v : E (i a)) :
    imageFiberCoordinateEquiv i U ident e (i a) ⟨a, ha, rfl⟩ v = e a ha (ident a v) := by
  have he : (⟨a, ha, rfl⟩ : i a ∈ i '' U).choose = a :=
    hi (⟨a, ha, rfl⟩ : i a ∈ i '' U).choose_spec.2
  have hgen : ∀ (q : A) (hq : q ∈ U) (hqi : i a = i q), q = a →
      (((continuousLinearFiberCast E hqi).trans (ident q)).trans (e q hq)) v =
        e a ha (ident a v) := by
    intro q hq hqi heq
    subst q
    rfl
  exact hgen _ _ _ he

/-- Promote an actual branch coframe chart through an open embedding. -/
def imageCanonicalPretrivialization (hi : IsOpenEmbedding i) (hU : IsOpen U) :
    Pretrivialization ℂ (π ℂ E) :=
  canonicalPretrivialization (i '' U) (hi.isOpenMap _ hU)
    (imageFiberCoordinateEquiv i U ident e)

theorem imageCanonicalPretrivialization_apply (hi : IsOpenEmbedding i) (hU : IsOpen U)
    (a : A) (ha : a ∈ U) (v : E (i a)) :
    imageCanonicalPretrivialization i U ident e hi hU ⟨i a, v⟩ =
      (i a, e a ha (ident a v)) := by
  rw [imageCanonicalPretrivialization, canonicalPretrivialization_apply (i '' U) _
    (imageFiberCoordinateEquiv i U ident e) (show i a ∈ i '' U from ⟨a, ha, rfl⟩),
    imageFiberCoordinateEquiv_apply i U ident e hi.injective]

instance imageCanonicalPretrivialization_complexLinear (hi : IsOpenEmbedding i) (hU : IsOpen U) :
    (imageCanonicalPretrivialization i U ident e hi hU).IsLinear ℂ :=
  canonicalPretrivialization_complexLinear _ _ _

instance imageCanonicalPretrivialization_realLinear
    [∀ x, Module ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
    (hi : IsOpenEmbedding i) (hU : IsOpen U) :
    (imageCanonicalPretrivialization i U ident e hi hU).IsLinear ℝ :=
  canonicalPretrivialization_realLinear _ _ _

theorem imageCanonicalPretrivialization_isInducing (hi : IsOpenEmbedding i) (hU : IsOpen U)
    {b : B} (hb : b ∈ i '' U) :
    IsInducing (imageCanonicalPretrivialization i U ident e hi hU ∘ Bundle.TotalSpace.mk b) :=
  canonicalPretrivialization_isInducing _ _ _ hb

end FsFltz.Geometry
