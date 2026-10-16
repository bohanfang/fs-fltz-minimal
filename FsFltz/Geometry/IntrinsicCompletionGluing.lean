import FsFltz.Geometry.IntrinsicCollarGluing
import Mathlib.Topology.Constructions
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Hausdorff

/-!
# Topological attachment of the full intrinsic completion end

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160, especially
142–158, and `sec:lean`, lines 805–821. The native collar parameter is inward.
This constructs the actual quotient attaching `t < δ`, with no lower bound,
to the original carrier by the proved one-sided collar `0 ≤ t < δ`.
The outward completion coordinate is `r = -t`. All native points remain.

This is a topological producer only. No completion object, flow, primitive,
marking, or smooth gluing certificate is supplied or asserted here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

section General

variable {M B : Type*} [TopologicalSpace M] [TopologicalSpace B]

/-- The actual half collar source, in the convention of the native collar. -/
abbrev Half (δ : ℝ) (B : Type*) := IntrinsicCollarGluing.Half δ B

/-- The half-infinite cylinder: negative native time has no lower bound. -/
abbrev Band (δ : ℝ) (B : Type*) := Iio δ ×ˢ (univ : Set B)

variable {δ : ℝ} (hδ : 0 < δ) (C : Half δ B → M)

/-- Regard a nonnegative cylinder point as a point of the proved half collar. -/
def halfOfNonneg (p : Band δ B) (hp : 0 ≤ p.val.1) : Half δ B :=
  ⟨p.val, ⟨hp, p.property.1⟩, mem_univ _⟩

/-- The nonnegative half collar embeds in the half-infinite cylinder. -/
def halfToBand (p : Half δ B) : Band δ B :=
  ⟨p.val, p.property.1.2, mem_univ _⟩

/-- Folding the new side onto the seam stays in the original half collar. -/
def foldBand (p : Band δ B) : Half δ B :=
  ⟨(max p.val.1 0, p.val.2), ⟨le_max_right _ _, max_lt p.property.1 hδ⟩,
    mem_univ _⟩

theorem continuous_foldBand : Continuous (foldBand hδ : Band δ B → Half δ B) := by
  exact (((continuous_fst.comp continuous_subtype_val).max continuous_const).prodMk
    (continuous_snd.comp continuous_subtype_val)).subtype_mk _

/-- Canonical representatives retain original points and exactly the new negative side. -/
def normalize : M ⊕ Band δ B → M ⊕ {p : Band δ B // p.val.1 < 0}
  | .inl x => .inl x
  | .inr p => if hp : 0 ≤ p.val.1 then .inl (C (halfOfNonneg p hp))
      else .inr ⟨p, lt_of_not_ge hp⟩

/-- The space is the quotient by literal identification of the same half collar. -/
def Space := Quotient (Setoid.ker (normalize C))

instance : TopologicalSpace (Space C) := inferInstanceAs
  (TopologicalSpace (Quotient (Setoid.ker (normalize C))))

/-- The original carrier in the constructed quotient. -/
def original (x : M) : Space C := Quotient.mk (Setoid.ker (normalize C)) (.inl x)

/-- The full half-infinite cylinder in the constructed quotient. -/
def cylinder (p : Band δ B) : Space C := Quotient.mk (Setoid.ker (normalize C)) (.inr p)

theorem continuous_original : Continuous (original C) :=
  (continuous_quotient_mk' (s := Setoid.ker (normalize C))).comp continuous_inl

theorem continuous_cylinder : Continuous (cylinder C) :=
  (continuous_quotient_mk' (s := Setoid.ker (normalize C))).comp continuous_inr

omit [TopologicalSpace M] [TopologicalSpace B] in
theorem original_injective : Function.Injective (original C) := by
  intro x y h
  exact Sum.inl.inj (Quotient.exact h)

omit [TopologicalSpace M] [TopologicalSpace B] in
theorem original_eq_cylinder_iff (x : M) (p : Band δ B) :
    original C x = cylinder C p ↔
      ∃ hp : 0 ≤ p.val.1, C (halfOfNonneg p hp) = x := by
  change Quotient.mk (Setoid.ker (normalize C)) (.inl x) =
    Quotient.mk (Setoid.ker (normalize C)) (.inr p) ↔ _
  rw [Quotient.eq]
  change Sum.inl x = normalize C (.inr p) ↔ _
  by_cases hp : 0 ≤ p.val.1
  · simp [normalize, hp, eq_comm]
  · simp [normalize, hp]

omit [TopologicalSpace M] [TopologicalSpace B] in
theorem cylinder_injective (hC : Function.Injective C) :
    Function.Injective (cylinder C) := by
  intro p q hpq
  have h := Quotient.exact hpq
  change normalize C (.inr p) = normalize C (.inr q) at h
  by_cases hp : 0 ≤ p.val.1 <;> by_cases hq : 0 ≤ q.val.1
  · simp only [normalize, hp, hq, ↓reduceDIte, Sum.inl.injEq] at h
    exact Subtype.ext (congrArg (fun z : Half δ B => z.val) (hC h))
  · simp [normalize, hp, hq] at h
  · simp [normalize, hp, hq] at h
  · simp only [normalize, hp, hq, ↓reduceDIte, Sum.inr.injEq] at h
    exact congrArg Subtype.val h

omit [TopologicalSpace M] [TopologicalSpace B] in
theorem original_collar_eq_cylinder (p : Half δ B) :
    original C (C p) = cylinder C (halfToBand p) := by
  apply (original_eq_cylinder_iff C _ _).mpr
  exact ⟨p.property.1.1, rfl⟩

omit [TopologicalSpace M] [TopologicalSpace B] in
theorem jointly_surjective (x : Space C) :
    (∃ y, original C y = x) ∨ ∃ p, cylinder C p = x := by
  induction x using Quotient.inductionOn with
  | h x => cases x with
    | inl y => exact Or.inl ⟨y, rfl⟩
    | inr p => exact Or.inr ⟨p, rfl⟩

theorem isOpen_space_iff (U : Set (Space C)) :
    IsOpen U ↔ IsOpen (original C ⁻¹' U) ∧ IsOpen (cylinder C ⁻¹' U) := by
  change IsOpen[TopologicalSpace.coinduced
    (Quotient.mk (Setoid.ker (normalize C))) inferInstance] U ↔ _
  rw [isOpen_coinduced, isOpen_sum_iff]
  rfl

theorem continuous_halfToBand : Continuous (halfToBand : Half δ B → Band δ B) :=
  continuous_subtype_val.subtype_mk _

omit [TopologicalSpace M] [TopologicalSpace B] in
theorem preimage_original_image_cylinder (U : Set (Band δ B)) :
    original C ⁻¹' (cylinder C '' U) = C '' (halfToBand ⁻¹' U) := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    obtain ⟨hn, hc⟩ := (original_eq_cylinder_iff C x p).mp hpx.symm
    exact ⟨halfOfNonneg p hn, hp, hc⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨halfToBand p, hp, (original_collar_eq_cylinder C p).symm⟩

/-- The actual cylinder is an open chart piece of the quotient. -/
theorem isOpenEmbedding_cylinder (hC : IsOpenEmbedding C) :
    IsOpenEmbedding (cylinder C) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_cylinder C) (cylinder_injective C hC.injective)
  intro U hU
  apply (isOpen_space_iff C _).mpr
  constructor
  · rw [preimage_original_image_cylinder C]
    exact hC.isOpenMap _ (hU.preimage (continuous_halfToBand))
  · rw [Set.preimage_image_eq _ (cylinder_injective C hC.injective)]
    exact hU

/-- The folding map on canonical representatives. -/
def foldNormal : M ⊕ {p : Band δ B // p.val.1 < 0} → M
  | .inl x => x
  | .inr p => C ⟨(0, p.val.val.2), ⟨le_rfl, hδ⟩, mem_univ _⟩

/-- A continuous retraction of the space onto the original carrier. -/
def fold : Space C → M :=
  Quotient.lift (foldNormal hδ C ∘ normalize C)
    (fun _ _ h => congrArg (foldNormal hδ C) h)

omit [TopologicalSpace M] [TopologicalSpace B] in
@[simp] theorem fold_original (x : M) : fold hδ C (original C x) = x := rfl

omit [TopologicalSpace M] [TopologicalSpace B] in
@[simp] theorem fold_cylinder (p : Band δ B) :
    fold hδ C (cylinder C p) = C (foldBand hδ p) := by
  change foldNormal hδ C (normalize C (.inr p)) = _
  by_cases hp : 0 ≤ p.val.1
  · simp only [normalize, hp, ↓reduceDIte, foldNormal]
    congr 1
    exact Subtype.ext (Prod.ext (max_eq_left hp).symm rfl)
  · simp only [normalize, hp, ↓reduceDIte, foldNormal]
    congr 1
    exact Subtype.ext (Prod.ext (max_eq_right (le_of_not_ge hp)).symm rfl)

theorem continuous_fold (hC : Continuous C) : Continuous (fold hδ C) := by
  apply Continuous.quotient_lift
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_id
  · change Continuous (fun p : Band δ B => fold hδ C (cylinder C p))
    simpa only [fold_cylinder, Function.comp_def] using hC.comp (continuous_foldBand hδ)

include hδ in
/-- Original points carry exactly their original topology. -/
theorem isEmbedding_original (hC : Continuous C) : IsEmbedding (original C) :=
  IsEmbedding.of_leftInverse (fold_original hδ C) (continuous_fold hδ C hC)
    (continuous_original C)

theorem isCompact_range_original [CompactSpace M] : IsCompact (range (original C)) :=
  isCompact_range (continuous_original C)

omit [TopologicalSpace M] [TopologicalSpace B] in
theorem fold_eq_and_ne_mem_cylinder {x y : Space C}
    (hf : fold hδ C x = fold hδ C y) (hne : x ≠ y) :
    x ∈ range (cylinder C) ∧ y ∈ range (cylinder C) := by
  rcases jointly_surjective C x with ⟨a, rfl⟩ | ⟨p, rfl⟩ <;>
    rcases jointly_surjective C y with ⟨b, rfl⟩ | ⟨q, rfl⟩
  · exact (hne (congrArg (original C) hf)).elim
  · rw [fold_original, fold_cylinder] at hf
    subst a
    exact ⟨⟨halfToBand (foldBand hδ q),
      (original_collar_eq_cylinder C _).symm⟩, mem_range_self _⟩
  · rw [fold_original, fold_cylinder] at hf
    subst b
    exact ⟨mem_range_self _, ⟨halfToBand (foldBand hδ p),
      (original_collar_eq_cylinder C _).symm⟩⟩
  · exact ⟨mem_range_self _, mem_range_self _⟩

include hδ in
/-- Hausdorffness is constructed from the native carrier and its actual collar.
Equal fold images of distinct points lie in the single Hausdorff cylinder chart. -/
theorem t2Space_space [T2Space M] [T2Space B] (hC : IsOpenEmbedding C) :
    T2Space (Space C) := by
  refine ⟨fun x y hne => ?_⟩
  by_cases hf : fold hδ C x = fold hδ C y
  · obtain ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩ := fold_eq_and_ne_mem_cylinder hδ C hf hne
    obtain ⟨U, V, hU, hV, hp, hq, hUV⟩ :=
      t2_separation (fun hpq => hne (congrArg (cylinder C) hpq))
    have he := isOpenEmbedding_cylinder C hC
    refine ⟨cylinder C '' U, cylinder C '' V, he.isOpenMap _ hU,
      he.isOpenMap _ hV, mem_image_of_mem _ hp, mem_image_of_mem _ hq, ?_⟩
    exact (Set.disjoint_image_iff he.injective).mpr hUV
  · obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := t2_separation hf
    have hc := continuous_fold hδ C hC.continuous
    exact ⟨fold hδ C ⁻¹' U, fold hδ C ⁻¹' V, hU.preimage hc,
      hV.preimage hc, hx, hy, hUV.preimage _⟩

include hδ in
/-- The original carrier is a closed embedded subspace of the constructed space. -/
theorem isClosedEmbedding_original [T2Space M] [T2Space B] (hC : IsOpenEmbedding C) :
    IsClosedEmbedding (original C) := by
  have := t2Space_space hδ C hC
  exact Function.LeftInverse.isClosedEmbedding (fold_original hδ C)
    (continuous_fold hδ C hC.continuous) (continuous_original C)

include hδ in
/-- Open subsets of the original carrier avoiding the seam remain open in the space. -/
theorem isOpen_original_image_of_seam_disjoint (hC : Continuous C)
    {U : Set M} (hU : IsOpen U)
    (hseam : ∀ b : B, C ⟨(0, b), ⟨le_rfl, hδ⟩, mem_univ _⟩ ∉ U) :
    IsOpen (original C '' U) := by
  apply (isOpen_space_iff C _).mpr
  constructor
  · rw [Set.preimage_image_eq _ (original_injective C)]
    exact hU
  · have heq : cylinder C ⁻¹' (original C '' U) =
        {p : Band δ B | 0 < p.val.1 ∧ C (foldBand hδ p) ∈ U} := by
      ext p
      constructor
      · rintro ⟨x, hx, hxp⟩
        obtain ⟨hp, hCp⟩ := (original_eq_cylinder_iff C x p).mp hxp
        have hne : p.val.1 ≠ 0 := by
          intro hz
          have hp0 : halfOfNonneg p hp =
              ⟨(0, p.val.2), ⟨le_rfl, hδ⟩, mem_univ _⟩ :=
            Subtype.ext (Prod.ext hz rfl)
          apply hseam p.val.2
          rw [← hp0, hCp]
          exact hx
        refine ⟨lt_of_le_of_ne hp hne.symm, ?_⟩
        have hh : foldBand hδ p = halfOfNonneg p hp :=
          Subtype.ext (Prod.ext (max_eq_left hp) rfl)
        rwa [hh, hCp]
      · rintro ⟨hp, hx⟩
        refine ⟨C (foldBand hδ p), hx, ?_⟩
        apply (original_eq_cylinder_iff C _ _).mpr
        refine ⟨hp.le, ?_⟩
        congr 1
        exact Subtype.ext (Prod.ext (max_eq_left hp.le).symm rfl)
    rw [heq]
    exact (isOpen_lt continuous_const (continuous_fst.comp continuous_subtype_val)).inter
      (hU.preimage (hC.comp (continuous_foldBand hδ)))

/-- The full outward cylinder. Its real parameter is not bounded above. -/
abbrev End (B : Type*) := Ici (0 : ℝ) ×ˢ (univ : Set B)

/-- Conversion from outward completion time to the inward native collar coordinate. -/
def endToBand (p : End B) : Band δ B :=
  ⟨(-p.val.1, p.val.2), lt_of_le_of_lt (neg_nonpos.mpr p.property.1) hδ,
    mem_univ _⟩

theorem continuous_endToBand : Continuous (endToBand hδ : End B → Band δ B) :=
  (((continuous_fst.comp continuous_subtype_val).neg).prodMk
    (continuous_snd.comp continuous_subtype_val)).subtype_mk _

/-- A continuous retraction of the half-infinite band onto its outward half. -/
def endFold (p : Band δ B) : End B :=
  ⟨(max (-p.val.1) 0, p.val.2), le_max_right (-p.val.1) (0 : ℝ), mem_univ _⟩

theorem continuous_endFold : Continuous (endFold : Band δ B → End B) :=
  ((((continuous_fst.comp continuous_subtype_val).neg).max continuous_const).prodMk
    (continuous_snd.comp continuous_subtype_val)).subtype_mk _

omit [TopologicalSpace M] [TopologicalSpace B] in
@[simp] theorem endFold_endToBand (p : End B) : endFold (endToBand hδ p) = p := by
  apply Subtype.ext
  exact Prod.ext (by simp [endFold, endToBand, max_eq_left (show 0 ≤ p.val.1 from p.property.1)]) rfl

/-- The change from outward time to the half-infinite band is an embedding. -/
theorem isEmbedding_endToBand : IsEmbedding (endToBand hδ : End B → Band δ B) :=
  IsEmbedding.of_leftInverse (endFold_endToBand hδ) continuous_endFold
    (continuous_endToBand hδ)

/-- The full outward end in the quotient, with radius `r = -t`. -/
def endIn (p : End B) : Space C := cylinder C (endToBand hδ p)

theorem continuous_endIn : Continuous (endIn hδ C) :=
  (continuous_cylinder C).comp (continuous_endToBand hδ)

/-- The completion contains an embedded copy of every nonnegative outward radius. -/
theorem isEmbedding_endIn (hC : IsOpenEmbedding C) : IsEmbedding (endIn hδ C) :=
  (isOpenEmbedding_cylinder C hC).isEmbedding.comp (isEmbedding_endToBand hδ)

omit [TopologicalSpace M] [TopologicalSpace B] in
/-- The full outward end meets native points exactly at radius zero. -/
theorem original_eq_endIn_iff (x : M) (p : End B) :
    original C x = endIn hδ C p ↔
      p.val.1 = 0 ∧ C ⟨(0, p.val.2), ⟨le_rfl, hδ⟩, mem_univ _⟩ = x := by
  rw [endIn, original_eq_cylinder_iff]
  constructor
  · rintro ⟨hp, hCp⟩
    have hr : p.val.1 = 0 := le_antisymm (neg_nonneg.mp hp) p.property.1
    refine ⟨hr, ?_⟩
    have he : halfOfNonneg (endToBand hδ p) hp =
        ⟨(0, p.val.2), ⟨le_rfl, hδ⟩, mem_univ _⟩ := by
      apply Subtype.ext
      exact Prod.ext (by simp [halfOfNonneg, endToBand, hr]) rfl
    rwa [he] at hCp
  · rintro ⟨hr, hCx⟩
    have hp : 0 ≤ (endToBand hδ p).val.1 := by simp [endToBand, hr]
    refine ⟨hp, ?_⟩
    have he : halfOfNonneg (endToBand hδ p) hp =
        ⟨(0, p.val.2), ⟨le_rfl, hδ⟩, mem_univ _⟩ := by
      apply Subtype.ext
      exact Prod.ext (by simp [halfOfNonneg, endToBand, hr]) rfl
    rwa [he]

omit [TopologicalSpace M] [TopologicalSpace B] in
/-- Native points and the full outward end cover the quotient. -/
theorem original_endIn_cover (x : Space C) :
    x ∈ range (original C) ∪ range (endIn hδ C) := by
  rcases jointly_surjective C x with ⟨a, rfl⟩ | ⟨p, rfl⟩
  · exact Or.inl (mem_range_self a)
  · by_cases hp : 0 ≤ p.val.1
    · exact Or.inl ⟨C (halfOfNonneg p hp),
        (original_eq_cylinder_iff C _ p).mpr ⟨hp, rfl⟩⟩
    · let q : End B := ⟨(-p.val.1, p.val.2), neg_nonneg.mpr (le_of_not_ge hp),
        mem_univ _⟩
      refine Or.inr ⟨q, ?_⟩
      change cylinder C (endToBand hδ q) = cylinder C p
      congr 1
      apply Subtype.ext
      exact Prod.ext (neg_neg _) rfl

omit [TopologicalSpace M] [TopologicalSpace B] in
/-- The strictly positive outward end is disjoint from the native carrier. -/
theorem disjoint_original_positive_endIn :
    Disjoint (range (original C)) (endIn hδ C '' {p : End B | 0 < p.val.1}) := by
  rw [Set.disjoint_left]
  rintro x ⟨a, rfl⟩ ⟨p, hp, hpa⟩
  have hz := ((original_eq_endIn_iff hδ C a p).mp hpa.symm).1
  exact (ne_of_gt hp) hz

/-- A bounded closed outward cylinder, inside the full outward end. -/
def boundedEnd (R : ℝ) : Set (End B) := {p | p.val.1 ≤ R}

/-- Bounded outward cylinders are compact when the boundary is compact. -/
theorem isCompact_boundedEnd [CompactSpace B] (R : ℝ) :
    IsCompact (boundedEnd (B := B) R) := by
  apply Subtype.isCompact_iff.mpr
  have he : Subtype.val '' boundedEnd (B := B) R = Icc 0 R ×ˢ (univ : Set B) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q.property.1, hq⟩, mem_univ _⟩
    · rintro ⟨hp, hb⟩
      exact ⟨⟨p, hp.1, hb⟩, hp.2, rfl⟩
  rw [he]
  exact isCompact_Icc.prod isCompact_univ

/-- The native compact piece enlarged by a bounded closed outward cylinder. -/
def truncation (R : ℝ) : Set (Space C) :=
  range (original C) ∪ endIn hδ C '' boundedEnd (B := B) R

/-- Every bounded enlargement of the native compact piece is compact. -/
theorem isCompact_truncation [CompactSpace M] [CompactSpace B] (R : ℝ) :
    IsCompact (truncation hδ C R) :=
  (isCompact_range_original C).union
    ((isCompact_boundedEnd R).image (continuous_endIn hδ C))

omit [TopologicalSpace M] [TopologicalSpace B] in
/-- Closed bounded enlargements form an increasing family. -/
theorem truncation_mono {R S : ℝ} (hRS : R ≤ S) :
    truncation hδ C R ⊆ truncation hδ C S := by
  apply union_subset_union_right
  apply image_mono
  exact fun _ hp => le_trans hp hRS

omit [TopologicalSpace M] [TopologicalSpace B] in
/-- Every quotient point occurs in an enlargement at a finite nonnegative radius. -/
theorem exists_mem_truncation (x : Space C) :
    ∃ R : ℝ, 0 ≤ R ∧ x ∈ truncation hδ C R := by
  rcases original_endIn_cover hδ C x with hx | ⟨p, rfl⟩
  · exact ⟨0, le_rfl, Or.inl hx⟩
  · exact ⟨p.val.1, p.property.1, Or.inr ⟨p, (show p.val.1 ≤ p.val.1 from le_rfl), rfl⟩⟩

end General

section Native

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : Half δ (IntrinsicBoundary.Point k M) → M)

/-- The literal native interior is the first open piece of the constructed space. -/
def interiorIn (x : IntrinsicInterior.Point k M) : Space C := original C x.val

include hδ in
/-- The native interior embeds openly; no space atlas is supplied. -/
theorem isOpenEmbedding_interiorIn (hC : IsOpenEmbedding C)
    (hboundary : ∀ p : Half δ (IntrinsicBoundary.Point k M),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C p) ↔ p.val.1 = 0) :
    IsOpenEmbedding (interiorIn C) := by
  have he : IsEmbedding (interiorIn C) :=
    (isEmbedding_original hδ C hC.continuous).comp
      IntrinsicInterior.isOpenEmbedding_val.isEmbedding
  refine ⟨he, ?_⟩
  have hr : range (interiorIn C) = original C '' (𝓡∂ (k + 1)).interior M := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => ⟨y.val, y.property, hy⟩,
      fun ⟨y, hy, hyx⟩ => ⟨⟨y, hy⟩, hyx⟩⟩
  rw [hr]
  apply isOpen_original_image_of_seam_disjoint hδ C hC.continuous
    IntrinsicInterior.isOpen_interior
  intro b hb
  exact ((𝓡∂ (k + 1)).isInteriorPoint_iff_not_isBoundaryPoint _).mp hb
    ((hboundary _).mpr rfl)

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The original interior and the new cylinder cover the constructed quotient. -/
theorem interior_cylinder_cover
    (hzero : ∀ b : IntrinsicBoundary.Point k M,
      C ⟨(0, b), ⟨le_rfl, hδ⟩, mem_univ _⟩ = b.val)
    (x : Space C) : x ∈ range (interiorIn C) ∪ range (cylinder C) := by
  rcases jointly_surjective C x with ⟨a, rfl⟩ | ⟨p, rfl⟩
  · rcases (𝓡∂ (k + 1)).isInteriorPoint_or_isBoundaryPoint a with hi | hb
    · exact Or.inl ⟨⟨a, hi⟩, rfl⟩
    · let b : IntrinsicBoundary.Point k M := ⟨a, hb⟩
      have hh := original_collar_eq_cylinder C
        (⟨(0, b), ⟨le_rfl, hδ⟩, mem_univ _⟩ : Half δ (IntrinsicBoundary.Point k M))
      rw [hzero b] at hh
      exact Or.inr ⟨_, hh.symm⟩
  · exact Or.inr (mem_range_self p)

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The overlap of the genuine open pieces is precisely the positive collar. -/
theorem interiorIn_eq_cylinder_iff
    (hboundary : ∀ p : Half δ (IntrinsicBoundary.Point k M),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C p) ↔ p.val.1 = 0)
    (x : IntrinsicInterior.Point k M) (p : Band δ (IntrinsicBoundary.Point k M)) :
    interiorIn C x = cylinder C p ↔
      ∃ hp : 0 < p.val.1, C (halfOfNonneg p hp.le) = x.val := by
  constructor
  · intro h
    obtain ⟨hp, hCp⟩ := (original_eq_cylinder_iff C x.val p).mp h
    have hne : p.val.1 ≠ 0 := by
      intro hz
      have hb := (hboundary (halfOfNonneg p hp)).mpr hz
      rw [hCp] at hb
      exact ((𝓡∂ (k + 1)).isInteriorPoint_iff_not_isBoundaryPoint _).mp x.property hb
    exact ⟨lt_of_le_of_ne hp hne.symm, hCp⟩
  · rintro ⟨hp, hCp⟩
    exact (original_eq_cylinder_iff C x.val p).mpr ⟨hp.le, hCp⟩

include hδ in
/-- Second countability follows from the actual two-piece open cover, including
the empty-boundary case. The full original-carrier quotient map need not be open. -/
theorem secondCountableTopology_space [SecondCountableTopology M]
    (hC : IsOpenEmbedding C)
    (hboundary : ∀ p : Half δ (IntrinsicBoundary.Point k M),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C p) ↔ p.val.1 = 0)
    (hzero : ∀ b : IntrinsicBoundary.Point k M,
      C ⟨(0, b), ⟨le_rfl, hδ⟩, mem_univ _⟩ = b.val) :
    SecondCountableTopology (Space C) := by
  let U : Bool → Set (Space C) := fun b =>
    if b then range (interiorIn C) else range (cylinder C)
  have hi := isOpenEmbedding_interiorIn hδ C hC hboundary
  have hc := isOpenEmbedding_cylinder C hC
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
      rcases interior_cylinder_cover hδ C hzero x with hx | hx
      · exact mem_iUnion.mpr ⟨true, hx⟩
      · exact mem_iUnion.mpr ⟨false, hx⟩

end Native

end FsFltz.Geometry.IntrinsicCompletionGluing
