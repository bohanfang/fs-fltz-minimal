import FsFltz.Geometry.IntrinsicCompletionGluing

/-!
# The finite native extension is an open piece of the full attachment

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158, and `sec:lean`,
lines 805–821. The inclusion constructed here fixes every native point and
every finite collar coordinate. It is intended to transport the already
constructed finite smooth neighborhood into the full topological attachment.
No smooth atlas or primitive on the full attachment is asserted here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {M B : Type*} [TopologicalSpace M] [TopologicalSpace B]
  {δ : ℝ} (C : Half δ B → M)

/-- The finite two-sided cylinder includes into the half-infinite cylinder
without changing its inward time coordinate. -/
def finiteBandIn (p : IntrinsicCollarGluing.Band δ B) : Band δ B :=
  ⟨p.val, p.property.1.2, mem_univ _⟩

theorem continuous_finiteBandIn :
    Continuous (finiteBandIn : IntrinsicCollarGluing.Band δ B → Band δ B) :=
  continuous_subtype_val.subtype_mk _

omit [TopologicalSpace M] [TopologicalSpace B] in
theorem finiteBandIn_injective : Function.Injective
    (finiteBandIn : IntrinsicCollarGluing.Band δ B → Band δ B) :=
  fun _ _ h => Subtype.ext (congrArg (fun p : Band δ B => p.val) h)

omit [TopologicalSpace M] [TopologicalSpace B] in
/-- The finite cylinder has exactly its literal coordinate range in the full band. -/
theorem range_finiteBandIn :
    range (finiteBandIn : IntrinsicCollarGluing.Band δ B → Band δ B) =
      {p : Band δ B | -δ < p.val.1} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact q.property.1.1
  · intro hp
    exact ⟨⟨p.val, ⟨hp, p.property.1⟩, mem_univ _⟩, rfl⟩

/-- The finite cylinder is the open interval `-δ < t < δ` in the full cylinder. -/
theorem isOpenEmbedding_finiteBandIn :
    IsOpenEmbedding (finiteBandIn : IntrinsicCollarGluing.Band δ B → Band δ B) := by
  have he : IsEmbedding (finiteBandIn : IntrinsicCollarGluing.Band δ B → Band δ B) :=
    IsEmbedding.of_comp continuous_finiteBandIn continuous_subtype_val
      IsEmbedding.subtypeVal
  refine ⟨he, ?_⟩
  rw [range_finiteBandIn]
  exact isOpen_lt continuous_const (continuous_fst.comp continuous_subtype_val)

/-- Inclusion of the canonical representatives of the finite quotient. -/
def finiteNormalIn : M ⊕ {p : IntrinsicCollarGluing.Band δ B // p.val.1 < 0} →
    M ⊕ {p : Band δ B // p.val.1 < 0} :=
  Sum.map id (fun p => ⟨finiteBandIn p.val, p.property⟩)

omit [TopologicalSpace M] [TopologicalSpace B] in
theorem normalize_finiteBandIn (p : M ⊕ IntrinsicCollarGluing.Band δ B) :
    normalize C (Sum.map id finiteBandIn p) =
      finiteNormalIn (IntrinsicCollarGluing.normalize C p) := by
  cases p with
  | inl x => rfl
  | inr p =>
    by_cases hp : 0 ≤ p.val.1 <;>
      simp [normalize, IntrinsicCollarGluing.normalize, finiteNormalIn,
        finiteBandIn, IntrinsicCollarGluing.halfOfNonneg, halfOfNonneg, hp]

/-- The actual finite native extension includes into the full attachment. -/
def finiteIn : IntrinsicCollarGluing.Extension C → Space C :=
  Quotient.map (Sum.map id finiteBandIn) (fun x y h => by
    change normalize C (Sum.map id finiteBandIn x) =
      normalize C (Sum.map id finiteBandIn y)
    rw [normalize_finiteBandIn, normalize_finiteBandIn]
    exact congrArg finiteNormalIn h)

omit [TopologicalSpace M] [TopologicalSpace B] in
@[simp] theorem finiteIn_original (x : M) :
    finiteIn C (IntrinsicCollarGluing.original C x) = original C x := rfl

omit [TopologicalSpace M] [TopologicalSpace B] in
@[simp] theorem finiteIn_cylinder (p : IntrinsicCollarGluing.Band δ B) :
    finiteIn C (IntrinsicCollarGluing.cylinder C p) = cylinder C (finiteBandIn p) := rfl

omit [TopologicalSpace M] [TopologicalSpace B] in
theorem finiteNormalIn_injective : Function.Injective
    (finiteNormalIn : M ⊕ {p : IntrinsicCollarGluing.Band δ B // p.val.1 < 0} →
      M ⊕ {p : Band δ B // p.val.1 < 0}) := by
  apply Sum.map_injective.mpr
  refine ⟨Function.injective_id, ?_⟩
  intro p q hpq
  apply Subtype.ext
  apply finiteBandIn_injective
  exact congrArg (fun z : {p : Band δ B // p.val.1 < 0} => z.val) hpq

omit [TopologicalSpace M] [TopologicalSpace B] in
/-- No native points or finite cylinder points are collapsed by the full attachment. -/
theorem finiteIn_injective : Function.Injective (finiteIn C) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      intro h
      apply Quotient.sound
      apply finiteNormalIn_injective
      have hh := Quotient.exact h
      change normalize C (Sum.map id finiteBandIn x) =
        normalize C (Sum.map id finiteBandIn y) at hh
      rwa [normalize_finiteBandIn, normalize_finiteBandIn] at hh

theorem continuous_finiteIn : Continuous (finiteIn C) := by
  apply Continuous.quotient_lift
  apply continuous_sum_dom.mpr
  exact ⟨continuous_original C,
    (continuous_cylinder C).comp continuous_finiteBandIn⟩

omit [TopologicalSpace M] [TopologicalSpace B] in
theorem preimage_original_image_finiteIn (U : Set (IntrinsicCollarGluing.Extension C)) :
    original C ⁻¹' (finiteIn C '' U) = IntrinsicCollarGluing.original C ⁻¹' U := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    have he : y = IntrinsicCollarGluing.original C x := finiteIn_injective C hyx
    rwa [he] at hy
  · intro hx
    exact ⟨IntrinsicCollarGluing.original C x, hx, rfl⟩

omit [TopologicalSpace M] [TopologicalSpace B] in
theorem preimage_cylinder_image_finiteIn (hδ : 0 < δ) (hC : Function.Injective C)
    (U : Set (IntrinsicCollarGluing.Extension C)) :
    cylinder C ⁻¹' (finiteIn C '' U) =
      finiteBandIn '' (IntrinsicCollarGluing.cylinder C ⁻¹' U) := by
  ext p
  constructor
  · rintro ⟨y, hy, hyx⟩
    rcases IntrinsicCollarGluing.jointly_surjective C y with ⟨a, rfl⟩ | ⟨q, rfl⟩
    · obtain ⟨hn, hc⟩ := (original_eq_cylinder_iff C a p).mp hyx
      let q := IntrinsicCollarGluing.halfToBand hδ (halfOfNonneg p hn)
      refine ⟨q, ?_, rfl⟩
      have hh := IntrinsicCollarGluing.original_collar_eq_cylinder hδ C
        (halfOfNonneg p hn)
      rw [hc] at hh
      change IntrinsicCollarGluing.cylinder C
        (IntrinsicCollarGluing.halfToBand hδ (halfOfNonneg p hn)) ∈ U
      rwa [← hh]
    · exact ⟨q, hy, cylinder_injective C hC hyx⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨IntrinsicCollarGluing.cylinder C q, hq, rfl⟩

/-- The existing finite native extension is an open embedded neighborhood in
the full topological attachment. Its map preserves the actual collar coordinate. -/
theorem isOpenEmbedding_finiteIn (hδ : 0 < δ) (hC : Function.Injective C) :
    IsOpenEmbedding (finiteIn C) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_finiteIn C) (finiteIn_injective C)
  intro U hU
  apply (isOpen_space_iff C _).mpr
  have hh := (IntrinsicCollarGluing.isOpen_extension_iff C U).mp hU
  constructor
  · rw [preimage_original_image_finiteIn]
    exact hh.1
  · rw [preimage_cylinder_image_finiteIn C hδ hC]
    exact isOpenEmbedding_finiteBandIn.isOpenMap _ hh.2

omit [TopologicalSpace M] [TopologicalSpace B] in
/-- The finite extension contains all native points and precisely the finite
collar window `-δ < t < δ` of the full cylinder. -/
theorem range_finiteIn :
    range (finiteIn C) = range (original C) ∪
      cylinder C '' {p : Band δ B | -δ < p.val.1} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rcases IntrinsicCollarGluing.jointly_surjective C y with ⟨a, rfl⟩ | ⟨p, rfl⟩
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨finiteBandIn p, p.property.1.1, rfl⟩
  · rintro (⟨a, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact ⟨IntrinsicCollarGluing.original C a, rfl⟩
    · exact ⟨IntrinsicCollarGluing.cylinder C
        ⟨p.val, ⟨hp, p.property.1⟩, mem_univ _⟩, rfl⟩

omit [TopologicalSpace M] [TopologicalSpace B] in
/-- In the actual outward coordinate, the finite patch is exactly `r < δ`. -/
theorem endIn_mem_range_finiteIn_iff (hδ : 0 < δ) (hC : Function.Injective C)
    (p : End B) : endIn hδ C p ∈ range (finiteIn C) ↔ p.val.1 < δ := by
  change endToBand hδ p ∈ cylinder C ⁻¹' (range (finiteIn C)) ↔ _
  rw [← image_univ, preimage_cylinder_image_finiteIn C hδ hC,
    preimage_univ, image_univ, range_finiteBandIn]
  change -δ < -p.val.1 ↔ p.val.1 < δ
  exact neg_lt_neg_iff

/-- The existing finite neighborhood is homeomorphic to its actual open image. -/
def finitePatchHomeomorph (hδ : 0 < δ) (hC : Function.Injective C) :
    IntrinsicCollarGluing.Extension C ≃ₜ range (finiteIn C) :=
  (isOpenEmbedding_finiteIn C hδ hC).isEmbedding.toHomeomorph

end FsFltz.Geometry.IntrinsicCompletionGluing
