import FsFltz.Geometry.IntrinsicCompletionAtlas

/-!
# Shared-parameter charts on the original completion quotients

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and
`sec:lean`, lines 788–814. This is the literal attachment for a varying
inward collar, with parameter preserved by its quotient relation. Its
fibers are the original slice quotients, including every native point.
The full cylinder is an open shared-parameter chart when the original
joint half collar is an open embedding.

The joint half-collar embedding is explicit geometric input here. This
module does not construct it from arbitrary compact bundles and does not
yet construct a smooth atlas on the entire completed total space.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

section NormalCoordinates

variable {M B : Type*} [TopologicalSpace M] [TopologicalSpace B]
  {δ : ℝ} (C : Half δ B → M)

/-- Canonical representatives are all native points and the strictly new
negative inward-time cylinder. This equivalence uses the actual quotient
relation, without an injectivity or collar regularity hypothesis. -/
def normalEquiv : Space C ≃ M ⊕ {p : Band δ B // p.val.1 < 0} where
  toFun := Quotient.lift (normalize C) (fun _ _ h => h)
  invFun
    | .inl x => original C x
    | .inr p => cylinder C p.val
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h x =>
      cases x with
      | inl x => rfl
      | inr p =>
        change (match normalize C (.inr p) with
          | .inl x => original C x
          | .inr q => cylinder C q.val) = cylinder C p
        by_cases hp : 0 ≤ p.val.1
        · simp only [normalize, hp, ↓reduceDIte]
          exact (original_eq_cylinder_iff C _ p).mpr ⟨hp, rfl⟩
        · simp only [normalize, hp, ↓reduceDIte]
  right_inv x := by
    cases x with
    | inl x => rfl
    | inr p =>
      change normalize C (.inr p.val) = .inr p
      simp only [normalize, not_le.mpr p.property, ↓reduceDIte]

omit [TopologicalSpace M] [TopologicalSpace B] in
@[simp] theorem normalEquiv_original (x : M) :
    normalEquiv C (original C x) = .inl x := rfl

omit [TopologicalSpace M] [TopologicalSpace B] in
@[simp] theorem normalEquiv_cylinder (p : Band δ B) :
    normalEquiv C (cylinder C p) = normalize C (.inr p) := rfl

end NormalCoordinates

section SharedParameter

variable {T M B : Type*} [TopologicalSpace T] [TopologicalSpace M]
  [TopologicalSpace B] {δ : ℝ} (C : T → Half δ B → M)

/-- The original varying collar, with its parameter retained literally. -/
def totalCollar (p : Half δ (T × B)) : T × M :=
  (p.val.2.1, C p.val.2.1 ⟨(p.val.1, p.val.2.2), p.property.1, mem_univ _⟩)

/-- The actual completion attachment over the common parameter space. -/
abbrev TotalSpace := Space (totalCollar C)

/-- Product cylinder coordinates only reorder the parameter and radius. -/
def parameterBandHomeomorph : T × Band δ B ≃ₜ Band δ (T × B) where
  toFun p := ⟨(p.2.val.1, (p.1, p.2.val.2)), p.2.property.1, mem_univ _⟩
  invFun p := (p.val.2.1, ⟨(p.val.1, p.val.2.2), p.property.1, mem_univ _⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
      (continuous_fst.prodMk
        (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))).subtype_mk _
  continuous_invFun :=
    (continuous_fst.comp (continuous_snd.comp continuous_subtype_val)).prodMk
      (((continuous_fst.comp continuous_subtype_val).prodMk
        (continuous_snd.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _)

/-- The cylinder patch retains the original parameter and all inward
radii below the common collar width, with no outward radius bound. -/
def totalCylinder (p : T × Band δ B) : TotalSpace C :=
  cylinder (totalCollar C) (parameterBandHomeomorph p)

/-- The shared cylinder chart is open across the native boundary seam.
Only the original joint half-collar embedding is assumed. -/
theorem isOpenEmbedding_totalCylinder
    (hC : IsOpenEmbedding (totalCollar C)) : IsOpenEmbedding (totalCylinder C) :=
  (isOpenEmbedding_cylinder (totalCollar C) hC).comp
    parameterBandHomeomorph.isOpenEmbedding

/-- Parameter is well defined on the original quotient: the attachment
identifies only points with the same parameter. -/
def parameter : TotalSpace C → T := Quotient.lift
  (fun p : (T × M) ⊕ Band δ (T × B) =>
    match p with | .inl x => x.1 | .inr q => q.val.2.1)
  (by
    intro p q h
    let b : (T × M) ⊕ {r : Band δ (T × B) // r.val.1 < 0} → T :=
      fun r => match r with | .inl x => x.1 | .inr s => s.val.val.2.1
    have hb (r : (T × M) ⊕ Band δ (T × B)) :
        b (normalize (totalCollar C) r) =
          (match r with | .inl x => x.1 | .inr s => s.val.2.1) := by
      cases r with
      | inl x => rfl
      | inr s =>
        by_cases hs : 0 ≤ s.val.1 <;> simp [normalize, hs, b, totalCollar, halfOfNonneg]
    exact (hb p).symm.trans ((congrArg b h).trans (hb q)))

omit [TopologicalSpace T] [TopologicalSpace M] [TopologicalSpace B] in
@[simp] theorem parameter_original (t : T) (x : M) :
    parameter C (original (totalCollar C) (t, x)) = t := rfl

omit [TopologicalSpace M] in
@[simp] theorem parameter_totalCylinder (p : T × Band δ B) :
    parameter C (totalCylinder C p) = p.1 := rfl

/-- The parameter projection is continuous for the actual quotient topology. -/
theorem continuous_parameter : Continuous (parameter C) := by
  apply Continuous.quotient_lift
  apply continuous_sum_dom.mpr
  exact ⟨continuous_fst, continuous_fst.comp (continuous_snd.comp continuous_subtype_val)⟩

private def insertNormal (t : T) : M ⊕ {p : Band δ B // p.val.1 < 0} →
    (T × M) ⊕ {p : Band δ (T × B) // p.val.1 < 0}
  | .inl x => .inl (t, x)
  | .inr p => .inr ⟨parameterBandHomeomorph (t, p.val), p.property⟩

omit [TopologicalSpace M] in
private theorem insertNormal_injective (t : T) : Function.Injective
    (insertNormal (δ := δ) (M := M) (B := B) t) := by
  intro x y h
  cases x <;> cases y
  · exact congrArg Sum.inl (Prod.mk.inj (Sum.inl.inj h)).2
  · simp only [insertNormal, reduceCtorEq] at h
  · simp only [insertNormal, reduceCtorEq] at h
  · apply congrArg Sum.inr
    apply Subtype.ext
    have hh := congrArg parameterBandHomeomorph.symm
      (congrArg Subtype.val (Sum.inr.inj h))
    simpa only [Homeomorph.symm_apply_apply, Prod.mk.injEq, true_and] using hh

/-- The original slice quotient embeds set-theoretically into the shared
quotient. This map retains native points and cylinder coordinates. -/
def sliceIn (t : T) (x : Space (C t)) : TotalSpace C :=
  (normalEquiv (totalCollar C)).symm (insertNormal t (normalEquiv (C t) x))

omit [TopologicalSpace M] in
@[simp] theorem sliceIn_original (t : T) (x : M) :
    sliceIn C t (original (C t) x) = original (totalCollar C) (t, x) := rfl

omit [TopologicalSpace M] in
@[simp] theorem sliceIn_cylinder (t : T) (p : Band δ B) :
    sliceIn C t (cylinder (C t) p) = totalCylinder C (t, p) := by
  apply (normalEquiv (totalCollar C)).injective
  rw [sliceIn, Equiv.apply_symm_apply]
  change insertNormal t (normalize (C t) (.inr p)) =
    normalize (totalCollar C) (.inr (parameterBandHomeomorph (t, p)))
  by_cases hp : 0 ≤ p.val.1 <;>
    simp [normalize, hp, insertNormal, parameterBandHomeomorph, totalCollar, halfOfNonneg]

/-- The canonical map from the original slice quotient to the shared
quotient is continuous for their actual attachment topologies. -/
theorem continuous_sliceIn (t : T) : Continuous (sliceIn C t) := by
  apply (isQuotientMap_quotient_mk' (s := Setoid.ker (normalize (C t)))).continuous_iff.mpr
  apply continuous_sum_dom.mpr
  constructor
  · change Continuous (fun x : M => sliceIn C t (original (C t) x))
    simpa only [sliceIn_original, Function.comp_def, id_eq] using (continuous_original (totalCollar C)).comp
      (continuous_const.prodMk continuous_id)
  · change Continuous (fun p : Band δ B => sliceIn C t (cylinder (C t) p))
    simpa only [sliceIn_cylinder, totalCylinder, Function.comp_def, id_eq] using
      ((continuous_cylinder (totalCollar C)).comp parameterBandHomeomorph.continuous).comp
        (continuous_const.prodMk continuous_id)

omit [TopologicalSpace M] in
@[simp] theorem parameter_sliceIn (t : T) (x : Space (C t)) :
    parameter C (sliceIn C t x) = t := by
  rcases jointly_surjective (C t) x with ⟨y, rfl⟩ | ⟨p, rfl⟩
  · rw [sliceIn_original, parameter_original]
  · rw [sliceIn_cylinder, parameter_totalCylinder]

/-- Every fiber of the actual shared quotient is precisely its original
completion quotient, retaining the entire compact carrier and the end. -/
def fiberEquiv (t : T) : Space (C t) ≃ {x : TotalSpace C // parameter C x = t} :=
  Equiv.ofBijective (fun x => ⟨sliceIn C t x, parameter_sliceIn C t x⟩) (by
    constructor
    · intro x y h
      apply (normalEquiv (C t)).injective
      apply insertNormal_injective t
      have hh := congrArg (fun x => normalEquiv (totalCollar C) x.val) h
      simpa only [sliceIn, Equiv.apply_symm_apply] using hh
    · rintro ⟨x, hx⟩
      rcases jointly_surjective (totalCollar C) x with ⟨⟨s, y⟩, rfl⟩ | ⟨p, rfl⟩
      · change s = t at hx
        subst s
        exact ⟨original (C t) y, Subtype.ext (sliceIn_original C t y)⟩
      · change p.val.2.1 = t at hx
        let q : Band δ B := ⟨(p.val.1, p.val.2.2), p.property.1, mem_univ _⟩
        refine ⟨cylinder (C t) q, Subtype.ext ?_⟩
        change sliceIn C t (cylinder (C t) q) = cylinder (totalCollar C) p
        rw [sliceIn_cylinder]
        apply congrArg (cylinder (totalCollar C))
        apply Subtype.ext
        exact Prod.ext rfl (Prod.ext hx.symm rfl))

omit [TopologicalSpace M] in
@[simp] theorem fiberEquiv_val (t : T) (x : Space (C t)) :
    (fiberEquiv C t x).val = sliceIn C t x := rfl

end SharedParameter

section NativeInterior

variable {T M : Type*} [TopologicalSpace T] [TopologicalSpace M] {k : ℕ}
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M] [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ) (C : T → Half δ (IntrinsicBoundary.Point k M) → M)
  (hzero : ∀ t b, C t ⟨(0, b), ⟨le_rfl, hδ⟩, mem_univ _⟩ = b.val)

/-- The actual original interior, with its unchanged parameter, in the
shared quotient. -/
def totalInterior (p : T × IntrinsicInterior.Point k M) : TotalSpace C :=
  original (totalCollar C) (p.1, p.2.val)

include hδ hzero

/-- The shared native interior is an open patch of the actual quotient.
This uses its inherited original topology, rather than a transported one. -/
theorem isOpenEmbedding_totalInterior (hC : IsOpenEmbedding (totalCollar C)) :
    IsOpenEmbedding (totalInterior C) := by
  have he : IsEmbedding (totalInterior C) :=
    (isEmbedding_original hδ (totalCollar C) hC.continuous).comp
      (IsEmbedding.id.prodMap IntrinsicInterior.isOpenEmbedding_val.isEmbedding)
  refine ⟨he, ?_⟩
  have hr : range (totalInterior C) =
      original (totalCollar C) '' (univ ×ˢ (𝓡∂ (k + 1)).interior M) := by
    ext x
    constructor
    · rintro ⟨⟨t, y⟩, rfl⟩
      exact ⟨(t, y.val), ⟨mem_univ _, y.property⟩, rfl⟩
    · rintro ⟨⟨t, y⟩, ⟨_, hy⟩, rfl⟩
      exact ⟨(t, ⟨y, hy⟩), rfl⟩
  rw [hr]
  apply isOpen_original_image_of_seam_disjoint hδ (totalCollar C) hC.continuous
    (isOpen_univ.prod IntrinsicInterior.isOpen_interior)
  rintro ⟨t, b⟩ ⟨_, hb⟩
  change C t ⟨(0, b), ⟨le_rfl, hδ⟩, mem_univ _⟩ ∈ (𝓡∂ (k + 1)).interior M at hb
  rw [hzero] at hb
  exact ((𝓡∂ (k + 1)).isInteriorPoint_iff_not_isBoundaryPoint _).mp hb b.property

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The original interiors and the full shared cylinders cover the
completed total space, including every native boundary point. -/
theorem totalInterior_cylinder_cover (x : TotalSpace C) :
    (∃ p, totalInterior C p = x) ∨ ∃ p, totalCylinder C p = x := by
  rcases jointly_surjective (totalCollar C) x with ⟨⟨t, y⟩, rfl⟩ | ⟨p, rfl⟩
  · rcases (𝓡∂ (k + 1)).isInteriorPoint_or_isBoundaryPoint y with hi | hb
    · exact Or.inl ⟨(t, ⟨y, hi⟩), rfl⟩
    · let b : IntrinsicBoundary.Point k M := ⟨y, hb⟩
      let p : Band δ (IntrinsicBoundary.Point k M) := ⟨(0, b), hδ, mem_univ _⟩
      refine Or.inr ⟨(t, p), ?_⟩
      change cylinder (totalCollar C) (parameterBandHomeomorph (t, p)) = _
      apply (original_eq_cylinder_iff (totalCollar C) _ _).mpr _ |>.symm
      exact ⟨le_rfl, Prod.ext rfl (hzero t b)⟩
  · exact Or.inr ⟨parameterBandHomeomorph.symm p,
      congrArg (cylinder (totalCollar C)) (parameterBandHomeomorph.apply_symm_apply p)⟩

omit hδ hzero [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The mixed patch overlap is exactly the original positive inward
collar, with the original parameter literally equal on both sides. -/
theorem totalInterior_eq_totalCylinder_iff
    (hboundary : ∀ t (q : Half δ (IntrinsicBoundary.Point k M)),
      (𝓡∂ (k + 1)).IsBoundaryPoint (C t q) ↔ q.val.1 = 0)
    (x : T × IntrinsicInterior.Point k M) (p : T × Band δ (IntrinsicBoundary.Point k M)) :
    totalInterior C x = totalCylinder C p ↔
      x.1 = p.1 ∧ ∃ hp : 0 < p.2.val.1, C p.1 (halfOfNonneg p.2 hp.le) = x.2.val := by
  change original (totalCollar C) (x.1, x.2.val) =
    cylinder (totalCollar C) (parameterBandHomeomorph p) ↔ _
  rw [original_eq_cylinder_iff]
  constructor
  · rintro ⟨hn, hc⟩
    have ht : p.1 = x.1 := congrArg Prod.fst hc
    have he : C p.1 (halfOfNonneg p.2 hn) = x.2.val := congrArg Prod.snd hc
    have hne : p.2.val.1 ≠ 0 := by
      intro hz
      have hb := (hboundary p.1 (halfOfNonneg p.2 hn)).mpr hz
      rw [he] at hb
      exact ((𝓡∂ (k + 1)).isInteriorPoint_iff_not_isBoundaryPoint _).mp x.2.property hb
    exact ⟨ht.symm, lt_of_le_of_ne hn hne.symm, he⟩
  · rintro ⟨ht, hp, he⟩
    exact ⟨hp.le, Prod.ext ht.symm he⟩

end NativeInterior

end FsFltz.Geometry.IntrinsicCompletionGluing
