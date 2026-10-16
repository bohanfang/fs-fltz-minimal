import FsFltz.Analysis.DominantFace
import FsFltz.ToricIntrinsicFaces
import FsFltz.ToricFanCompleteness

/-!
# Native open stars and common-face smoothing geometry

Source: `geometric-part-fsf-proof.tex`, `eq:openstar`, lines 536–555,
and `lem:potential`, lines 588–611. All cones below are the literal
`faceFan` of the original `ToricInput`. The common-face tolerance reuses
`uniform_pairingGap_face`; no fan axiom or desired potential is an input.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators Topology

variable {n : ℕ}

/-- The source's union of closed cones containing the ray generator. -/
def rayStar (I : ToricInput n) (v : Lattice n) : Set (RealSpace n) :=
  {p | ∃ σ ∈ faceFan I, latticeReal v ∈ σ ∧ p ∈ σ}

/-- The finite fan is a subfamily of the cones on subsets of its actual
finite vertex set, together with its zero member. -/
theorem ToricInput.finite_faceFan (I : ToricInput n) : (faceFan I).Finite := by
  classical
  apply ((I.vertices.powerset.finite_toSet.image positiveCone).insert {0}).subset
  intro σ hσ
  rcases hσ with rfl | ⟨s, hs, _, _, rfl⟩
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨s, Finset.mem_powerset.mpr hs.1, rfl⟩

/-- The zero cone also has a proper supporting-face presentation. -/
theorem ToricInput.exists_proper_face_of_mem_faceFan (I : ToricInput n)
    {σ : Set (RealSpace n)} (hσ : σ ∈ faceFan I) :
    ∃ s, IsPolytopeFace I.vertices s ∧ s ≠ I.vertices ∧ σ = positiveCone s := by
  rcases hσ with rfl | ⟨s, hs, _, hp, he⟩
  · refine ⟨∅, isPolytopeFace_empty _, ?_, positiveCone_empty.symm⟩
    exact fun he => by simpa [← he] using I.vertices_nonempty
  · exact ⟨s, hs, hp, he⟩

private def realVertexSumLinearMap (s : Finset (Lattice n)) :
    ({v : Lattice n // v ∈ s} → ℝ) →ₗ[ℝ] RealSpace n where
  toFun a := ∑ v, a v • latticeReal v.val
  map_add' a b := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r a := by simp [smul_smul, Finset.smul_sum, smul_eq_mul]

private theorem realVertexSum_coefficient {s t : Finset (Lattice n)}
    (hst : s ⊆ t) (b : Module.Basis {v : Lattice n // v ∈ t} ℤ (Lattice n))
    (hb : ∀ v, b v = v.val) (v : {v : Lattice n // v ∈ s}) :
    ∃ L : RealSpace n →ₗ[ℝ] ℝ, ∀ a, L (realVertexSumLinearMap s a) = a v := by
  classical
  let i : {v : Lattice n // v ∈ t} := ⟨v.val, hst v.property⟩
  let L : Lattice n →ₗ[ℤ] ℝ := b.constr ℝ fun w => if w = i then 1 else 0
  have hL (w : {v : Lattice n // v ∈ s}) :
      L w.val = if w = v then 1 else 0 := by
    rw [← hb ⟨w.val, hst w.property⟩]
    change (b.constr ℝ (fun w => if w = i then 1 else 0))
      (b ⟨w.val, hst w.property⟩) = _
    rw [b.constr_basis]
    have he : (⟨w.val, hst w.property⟩ : {v : Lattice n // v ∈ t}) = i ↔ w = v := by
      simp only [i, Subtype.ext_iff]
    simp only [he]
  exact ⟨realExtension L, fun a => by
    simp [realVertexSumLinearMap, map_sum, map_smul, hL, smul_eq_mul]⟩

/-- Proper face cones are closed: their nonnegative coefficient orthants
map by an injective finite-dimensional linear map. -/
theorem ToricInput.isClosed_positiveCone (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hproper : s ≠ I.vertices) : IsClosed (positiveCone s) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · rw [positiveCone_empty]
    exact isClosed_singleton
  obtain ⟨t, _, hst, b, hb⟩ := I.exists_facet_basis_containing_face hs hne hproper
  have hinj : Function.Injective (realVertexSumLinearMap s) := by
    intro a c he
    funext v
    obtain ⟨L, hL⟩ := realVertexSum_coefficient hst b hb v
    exact (hL a).symm.trans ((congrArg L he).trans (hL c))
  have hclosed : IsClosed {a : {v : Lattice n // v ∈ s} → ℝ | ∀ v, 0 ≤ a v} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_le continuous_const (continuous_apply v)
  have heq : positiveCone s = realVertexSumLinearMap s ''
      {a : {v : Lattice n // v ∈ s} → ℝ | ∀ v, 0 ≤ a v} := by
    ext p
    constructor
    · rintro ⟨a, ha, he⟩
      refine ⟨fun v => a v.val, fun v => ha v.val v.property, ?_⟩
      change (∑ v : {v : Lattice n // v ∈ s}, a v.val • latticeReal v.val) = p
      rw [Finset.sum_coe_sort s (fun v => a v • latticeReal v), ← he]
    · rintro ⟨a, ha, rfl⟩
      let A : Lattice n → ℝ := fun v => if hv : v ∈ s then a ⟨v, hv⟩ else 0
      refine ⟨A, ?_, ?_⟩
      · intro v hv
        simpa [A, hv] using ha ⟨v, hv⟩
      · change (∑ v : {v : Lattice n // v ∈ s}, a v • latticeReal v.val) = _
        rw [← Finset.sum_coe_sort s (fun v => A v • latticeReal v)]
        apply Finset.sum_congr rfl
        intro v _
        simp [A, v.property]
  rw [heq]
  exact (LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)).isClosedMap _ hclosed

/-- Every actual cone in the original fan is closed. -/
theorem ToricInput.isClosed_of_mem_faceFan (I : ToricInput n)
    {σ : Set (RealSpace n)} (hσ : σ ∈ faceFan I) : IsClosed σ := by
  obtain ⟨s, hs, hp, rfl⟩ := I.exists_proper_face_of_mem_faceFan hσ
  exact I.isClosed_positiveCone hs hp

/-- Each cone in the native fan is closed under nonnegative scaling. -/
theorem ToricInput.smul_mem_of_mem_faceFan (I : ToricInput n)
    {σ : Set (RealSpace n)} (hσ : σ ∈ faceFan I)
    {p : RealSpace n} (hp : p ∈ σ) {r : ℝ} (hr : 0 ≤ r) : r • p ∈ σ := by
  obtain ⟨s, _, _, rfl⟩ := I.exists_proper_face_of_mem_faceFan hσ
  exact smul_mem_positiveCone hr hp

/-- The intersection face law in its additive form: if a sum of two
points of one fan cone belongs to a second, both summands belong to it. -/
theorem ToricInput.mem_of_add_mem_faceFan (I : ToricInput n)
    {σ τ : Set (RealSpace n)} (hσ : σ ∈ faceFan I) (hτ : τ ∈ faceFan I)
    {p q : RealSpace n} (hp : p ∈ σ) (hq : q ∈ σ) (hpq : p + q ∈ τ) :
    p ∈ τ ∧ q ∈ τ := by
  obtain ⟨s, hs, hsproper, rfl⟩ := I.exists_proper_face_of_mem_faceFan hσ
  obtain ⟨t, ht, htproper, rfl⟩ := I.exists_proper_face_of_mem_faceFan hτ
  obtain ⟨L, hL, he⟩ := I.positiveCone_inter_eq_supporting_slice hs ht hsproper htproper
  have hsum : L (p + q) = 0 :=
    ((Set.ext_iff.mp he (p + q)).mp ⟨add_mem_positiveCone hp hq, hpq⟩).2
  rw [map_add] at hsum
  have hpzero : L p = 0 := by linarith [hL p hp, hL q hq]
  have hqzero : L q = 0 := by linarith [hL p hp, hL q hq]
  exact ⟨((Set.ext_iff.mp he p).mpr ⟨hp, hpzero⟩).2,
    ((Set.ext_iff.mp he q).mpr ⟨hq, hqzero⟩).2⟩

/-- Native open-star characterization without choosing a presentation
of the minimal cone: every cone containing the point contains the ray.
The reverse direction uses finiteness, closedness and completeness;
the forward direction uses the exposed intersection face law. -/
theorem ToricInput.mem_interior_rayStar_iff (I : ToricInput n)
    (v : Lattice n) (p : RealSpace n) :
    p ∈ interior (rayStar I v) ↔
      ∀ σ ∈ faceFan I, p ∈ σ → latticeReal v ∈ σ := by
  constructor
  · intro hp σ hσ hpσ
    have hcont : ContinuousAt (fun t : ℝ => p - t • latticeReal v) 0 :=
      continuousAt_const.sub (continuousAt_id.smul continuousAt_const)
    have hev : ∀ᶠ t : ℝ in 𝓝 0, p - t • latticeReal v ∈ rayStar I v :=
      hcont.eventually_mem (by simpa using mem_interior_iff_mem_nhds.mp hp)
    obtain ⟨t, ht, τ, hτ, hvτ, hptτ⟩ := hev.exists_gt
    have htvτ := I.smul_mem_of_mem_faceFan hτ hvτ ht.le
    have hsum : (p - t • latticeReal v) + t • latticeReal v ∈ σ := by
      simpa using hpσ
    have htvσ := (I.mem_of_add_mem_faceFan hτ hσ hptτ htvτ hsum).2
    have hinv := I.smul_mem_of_mem_faceFan hσ htvσ (inv_pos.mpr ht).le
    simpa only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using hinv
  · intro hall
    let B : Set (Set (RealSpace n)) := {σ | σ ∈ faceFan I ∧ latticeReal v ∉ σ}
    have hfinite : B.Finite := I.finite_faceFan.subset fun _ h => h.1
    have hclosed : IsClosed (⋃₀ B) :=
      hfinite.isClosed_sUnion fun σ hσ => I.isClosed_of_mem_faceFan hσ.1
    have hpB : p ∈ (⋃₀ B)ᶜ := by
      rintro ⟨σ, ⟨hσ, hvσ⟩, hpσ⟩
      exact hvσ (hall σ hσ hpσ)
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (hclosed.isOpen_compl.mem_nhds hpB)
    intro q hq
    obtain ⟨σ, hσ, hqσ⟩ := I.exists_mem_faceFan q
    refine ⟨σ, hσ, ?_, hqσ⟩
    by_contra hvσ
    exact hq ⟨σ, ⟨hσ, hvσ⟩, hqσ⟩

/-- A positive coefficient at a face generator forces that generator
into every native fan cone containing the weighted sum. -/
theorem ToricInput.generator_mem_of_sum_mem_faceFan (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hproper : s ≠ I.vertices) (a : Lattice n → ℝ)
    (ha : ∀ w ∈ s, 0 ≤ a w) {v : Lattice n} (hv : v ∈ s) (hav : 0 < a v)
    {σ : Set (RealSpace n)} (hσ : σ ∈ faceFan I)
    (hpσ : (∑ w ∈ s, a w • latticeReal w) ∈ σ) : latticeReal v ∈ σ := by
  obtain ⟨t, ht, htproper, rfl⟩ := I.exists_proper_face_of_mem_faceFan hσ
  obtain ⟨L, hL, he⟩ := I.positiveCone_inter_eq_supporting_slice hs ht hproper htproper
  have hp : (∑ w ∈ s, a w • latticeReal w) ∈ positiveCone s := ⟨a, ha, rfl⟩
  have hz : L (∑ w ∈ s, a w • latticeReal w) = 0 :=
    ((Set.ext_iff.mp he _).mp ⟨hp, hpσ⟩).2
  simp only [map_sum, map_smul, smul_eq_mul] at hz
  have hterms : ∀ w ∈ s, a w * L (latticeReal w) ≤ 0 := fun w hw =>
    mul_nonpos_of_nonneg_of_nonpos (ha w hw) (hL _ (latticeReal_mem_positiveCone hw))
  have hvzero := (Finset.sum_eq_zero_iff_of_nonpos hterms).mp hz v hv
  have hLv : L (latticeReal v) = 0 :=
    (mul_eq_zero.mp hvzero).resolve_left hav.ne'
  exact ((Set.ext_iff.mp he _).mpr ⟨latticeReal_mem_positiveCone hv, hLv⟩).2

/-- The smoothing consumer of `eq:openstar`: a nonnegative average of
one proper face with positive weight at `v` lies in its open star. -/
theorem ToricInput.sum_mem_interior_rayStar (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hproper : s ≠ I.vertices) (a : Lattice n → ℝ)
    (ha : ∀ w ∈ s, 0 ≤ a w) {v : Lattice n} (hv : v ∈ s) (hav : 0 < a v) :
    (∑ w ∈ s, a w • latticeReal w) ∈ interior (rayStar I v) := by
  apply (I.mem_interior_rayStar_iff v _).mpr
  intro σ hσ hpσ
  exact I.generator_mem_of_sum_mem_faceFan hs hproper a ha hv hav hσ hpσ

/-- Adding an exactly maximizing vertex preserves the small-deficit
common-face conclusion needed by convolution smoothing. -/
theorem ToricInput.uniform_pairingGap_face_insert (I : ToricInput n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : RealSpace n, u ≠ 0 →
      ∀ s, s ⊆ I.vertices →
      (∀ w ∈ s, supportHeight I u - pairing w u ≤ ε * ‖u‖) →
      ∀ v ∈ I.vertices, pairing v u = supportHeight I u →
      ∃ t, IsPolytopeFace I.vertices t ∧ t.Nonempty ∧ t ≠ I.vertices ∧
        insert v s ⊆ t := by
  classical
  obtain ⟨ε, hε, hface⟩ := I.uniform_pairingGap_face
  refine ⟨ε, hε, ?_⟩
  intro u hu s hs hgap v hv hvmax
  apply hface u hu (insert v s) (Finset.insert_subset hv hs)
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | hw
  · rw [hvmax, sub_self]
    exact mul_nonneg hε.le (norm_nonneg _)
  · exact hgap w hw

/-- A single tolerance turns the nonnegative weighted normal arising in
support-height smoothing into an open-star point whenever its weight at
the prescribed generator is positive. Zero weights need no deficit bound. -/
theorem ToricInput.uniform_weighted_sum_mem_interior_rayStar (I : ToricInput n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : RealSpace n, u ≠ 0 →
      ∀ a : Lattice n → ℝ, (∀ w ∈ I.vertices, 0 ≤ a w) →
      (∀ w ∈ I.vertices, 0 < a w →
        supportHeight I u - pairing w u ≤ ε * ‖u‖) →
      ∀ v ∈ I.vertices, 0 < a v →
      (∑ w ∈ I.vertices, a w • latticeReal w) ∈ interior (rayStar I v) := by
  classical
  obtain ⟨ε, hε, hface⟩ := I.uniform_pairingGap_face
  refine ⟨ε, hε, ?_⟩
  intro u hu a ha hgap v hv hav
  let s := I.vertices.filter fun w => 0 < a w
  have hs : s ⊆ I.vertices := Finset.filter_subset _ _
  have hsgap : ∀ w ∈ s, supportHeight I u - pairing w u ≤ ε * ‖u‖ := by
    intro w hw
    exact hgap w (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hw).2
  obtain ⟨t, ht, _, htproper, hst⟩ := hface u hu s hs hsgap
  have hvt : v ∈ t := hst (Finset.mem_filter.mpr ⟨hv, hav⟩)
  have heq : (∑ w ∈ I.vertices, a w • latticeReal w) =
      ∑ w ∈ t, a w • latticeReal w := by
    symm
    apply Finset.sum_subset ht.1
    intro w hw hwt
    have haw : a w = 0 := by
      apply le_antisymm _ (ha w hw)
      apply le_of_not_gt
      intro haw
      exact hwt (hst (Finset.mem_filter.mpr ⟨hw, haw⟩))
    simp [haw]
  rw [heq]
  exact I.sum_mem_interior_rayStar ht htproper a (fun w hw => ha w (ht.1 hw)) hvt hav

/-- The open star is invariant under positive scaling, as required when
the radial gauge gradient is a positive multiple of the smoothed normal. -/
theorem ToricInput.smul_mem_interior_rayStar_iff (I : ToricInput n)
    (v : Lattice n) (p : RealSpace n) {r : ℝ} (hr : 0 < r) :
    r • p ∈ interior (rayStar I v) ↔ p ∈ interior (rayStar I v) := by
  rw [I.mem_interior_rayStar_iff, I.mem_interior_rayStar_iff]
  constructor
  · intro h σ hσ hp
    exact h σ hσ (I.smul_mem_of_mem_faceFan hσ hp hr.le)
  · intro h σ hσ hp
    have hpinv := I.smul_mem_of_mem_faceFan hσ hp (inv_pos.mpr hr).le
    have hpσ : p ∈ σ := by
      simpa only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using hpinv
    exact h σ hσ hpσ

/-- The same quantitative weighted-normal theorem with the native finite
vertex subtype indexing used by convolution coefficients. -/
theorem ToricInput.uniform_subtype_sum_mem_interior_rayStar (I : ToricInput n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : RealSpace n, u ≠ 0 →
      ∀ a : {v : Lattice n // v ∈ I.vertices} → ℝ, (∀ w, 0 ≤ a w) →
      (∀ w, 0 < a w → supportHeight I u - pairing w.val u ≤ ε * ‖u‖) →
      ∀ v, 0 < a v →
      (∑ w : {v : Lattice n // v ∈ I.vertices}, a w • latticeReal w.val) ∈
        interior (rayStar I v.val) := by
  classical
  obtain ⟨ε, hε, hstar⟩ := I.uniform_weighted_sum_mem_interior_rayStar
  refine ⟨ε, hε, ?_⟩
  intro u hu a ha hgap v hav
  let A : Lattice n → ℝ := fun w => if hw : w ∈ I.vertices then a ⟨w, hw⟩ else 0
  have hA (w : {w : Lattice n // w ∈ I.vertices}) : A w.val = a w := by
    simp [A, w.property]
  have hnonneg : ∀ w ∈ I.vertices, 0 ≤ A w := by
    intro w hw
    simpa only [hA ⟨w, hw⟩] using ha ⟨w, hw⟩
  have hdeficit : ∀ w ∈ I.vertices, 0 < A w →
      supportHeight I u - pairing w u ≤ ε * ‖u‖ := by
    intro w hw haw
    rw [hA ⟨w, hw⟩] at haw
    exact hgap ⟨w, hw⟩ haw
  have h := hstar u hu A hnonneg hdeficit v.val v.property (by simpa only [hA] using hav)
  rw [← Finset.sum_coe_sort I.vertices (fun w => A w • latticeReal w)] at h
  simpa only [hA] using h

/-- Nonnegative support-height homogeneity, needed to normalize polar
facet points along the radial gauge. -/
theorem ToricInput.supportHeight_smul_of_nonneg (I : ToricInput n)
    {r : ℝ} (hr : 0 ≤ r) (u : RealSpace n) :
    supportHeight I (r • u) = r * supportHeight I u := by
  apply le_antisymm
  · obtain ⟨v, hv⟩ := I.supportHeight_attained (r • u)
    rw [← hv, pairing_smul_real]
    exact mul_le_mul_of_nonneg_left (I.pairing_le_supportHeight u v) hr
  · obtain ⟨v, hv⟩ := I.supportHeight_attained u
    rw [← hv, ← pairing_smul_real]
    exact I.pairing_le_supportHeight (r • u) v

end FsFltz
