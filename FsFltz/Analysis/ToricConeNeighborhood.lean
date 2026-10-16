import FsFltz.Analysis.PolarFanGeometry
import FsFltz.ToricFaceTorus
import FsFltz.Analysis.TailoringCriticalToriReduced

/-!
# Full-span neighborhoods in the smallest face cone

Source: `geometric-part-fsf-proof.tex`, `lem:invariance`, lines 1648–1658.
Positive support coefficients produce an actual face whose full span is
locally contained in its positive cone. This is the local geometric input
for the retraction-flow argument, including points on larger cone faces.
-/

noncomputable section
open Set Filter Function
open scoped Topology BigOperators

namespace FsFltz

variable {n : ℕ}

theorem faceNormalMap_mem_positiveCone {s : Finset (Lattice n)}
    (a : s → ℝ) (ha : ∀ v, 0 ≤ a v) : faceNormalMap s a ∈ positiveCone s := by
  classical
  let A : Lattice n → ℝ := fun v => if hv : v ∈ s then a ⟨v, hv⟩ else 0
  refine ⟨A, ?_, ?_⟩
  · intro v hv
    simpa [A, hv] using ha ⟨v, hv⟩
  · rw [faceNormalMap_apply, ← Finset.sum_coe_sort s]
    apply Finset.sum_congr rfl
    intro v _
    simp [A, v.property]

/-- A strictly positive face combination is an interior point relative to
the full real span, expressed as an actual ambient neighborhood. -/
theorem ToricInput.eventually_span_mem_positiveCone
    (I : ToricInput n) {s : Finset (Lattice n)}
    (hs : IsPolytopeFace I.vertices s) (hsne : s.Nonempty)
    (hsproper : s ≠ I.vertices) (a : s → ℝ) (ha : ∀ v, 0 < a v) :
    ∀ᶠ q in 𝓝 (faceNormalMap s a),
      q ∈ Submodule.span ℝ (positiveCone s) → q ∈ positiveCone s := by
  classical
  let A := (faceNormalMap s).toLinearMap
  have hinj : Injective A :=
    faceNormalMap_injective_of_surjective (I.faceLevelMap_surjective hs hsne hsproper)
  obtain ⟨B, hB⟩ := A.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  have hBA (b : s → ℝ) : B (faceNormalMap s b) = b :=
    congrArg (fun L : (s → ℝ) →ₗ[ℝ] (s → ℝ) => L b) hB
  have hcone : positiveCone s ⊆ A.range := by
    rintro q ⟨b, _, hb⟩
    refine ⟨fun v => b v.val, ?_⟩
    change faceNormalMap s (fun v => b v.val) = q
    rw [faceNormalMap_apply, Finset.sum_coe_sort s (fun v => b v • latticeReal v), ← hb]
  have hspan : Submodule.span ℝ (positiveCone s) ≤ A.range :=
    Submodule.span_le.mpr hcone
  have hpos : ∀ᶠ q in 𝓝 (faceNormalMap s a), ∀ v, 0 < B q v := by
    apply eventually_all.mpr
    intro v
    have hcont : Continuous (fun q => B q v) :=
      (continuous_apply v).comp B.continuous_of_finiteDimensional
    exact hcont.continuousAt (lt_mem_nhds (by simpa only [hBA] using ha v))
  filter_upwards [hpos] with q hq
  intro hqs
  obtain ⟨b, hb⟩ := hspan hqs
  have hrec : faceNormalMap s (B q) = q := by
    change faceNormalMap s b = q at hb
    rw [← hb, hBA]
  rw [← hrec]
  exact faceNormalMap_mem_positiveCone _ (fun v => (hq v).le)

/-- Every nonzero point of a fan cone belongs to a smaller genuine face
whose full span is locally contained in that face cone. -/
theorem ToricInput.exists_face_span_neighborhood
    (I : ToricInput n) {σ : Set (RealSpace n)} (hσ : σ ∈ faceFan I)
    {p : RealSpace n} (hp : p ∈ σ) (hpne : p ≠ 0) :
    ∃ s : Finset (Lattice n), IsPolytopeFace I.vertices s ∧ s.Nonempty ∧
      s ≠ I.vertices ∧ p ∈ positiveCone s ∧ positiveCone s ⊆ σ ∧
      coneTorus σ ⊆ coneTorus (positiveCone s) ∧
      ∀ᶠ q in 𝓝 p, q ∈ Submodule.span ℝ (positiveCone s) → q ∈ positiveCone s := by
  classical
  obtain ⟨t, ht, htproper, rfl⟩ := I.exists_proper_face_of_mem_faceFan hσ
  obtain ⟨a, ha, he⟩ := hp
  let s := t.filter fun v => 0 < a v
  have hst : s ⊆ t := Finset.filter_subset _ _
  have he' : p = ∑ v ∈ s, a v • latticeReal v := by
    rw [he]
    symm
    apply Finset.sum_subset hst
    intro v hv hvs
    have hz : a v = 0 := le_antisymm
      (le_of_not_gt (fun h => hvs (Finset.mem_filter.mpr ⟨hv, h⟩))) (ha v hv)
    simp [hz]
  have hsne : s.Nonempty := by
    by_contra h
    have hz := Finset.not_nonempty_iff_eq_empty.mp h
    apply hpne
    simpa [hz] using he'
  have hsproper : s ≠ I.vertices := by
    intro h
    exact htproper (Finset.Subset.antisymm ht.1 (h ▸ hst))
  have hs := I.isPolytopeFace_subset ht htproper hst
  have hpositive : ∀ v : s, 0 < a v.val := fun v => (Finset.mem_filter.mp v.property).2
  have hpA : p = faceNormalMap s (fun v => a v.val) := by
    rw [faceNormalMap_apply, Finset.sum_coe_sort s (fun v => a v • latticeReal v)]
    exact he'
  refine ⟨s, hs, hsne, hsproper, ?_, positiveCone_mono hst, ?_, ?_⟩
  · rw [hpA]
    exact faceNormalMap_mem_positiveCone _ (fun v => (hpositive v).le)
  · intro θ hθ v hv
    exact hθ v (positiveCone_mono hst hv)
  · rw [hpA]
    exact I.eventually_span_mem_positiveCone hs hsne hsproper _ hpositive

end FsFltz
