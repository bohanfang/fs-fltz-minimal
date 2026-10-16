import FsFltz.Analysis.CompatiblePotentialExistence
import FsFltz.Analysis.HomogeneousPotential
import FsFltz.Analysis.SupportHeightBounds

/-!
# Angular exclusion for the strongly compatible potential

Source: `geometric-part-fsf-proof.tex`, `lem:gap`, `eq:phasegap`,
lines 651–658 and 671–677. The strong facet-star condition excludes an
outside vertex from the maximizing set. Compactness of the prescribed
Euclidean unit sphere then gives a quantitative homogeneous gap.
-/

noncomputable section

open Set
open scoped Topology ContDiff

namespace FsFltz

variable {n : ℕ} {I : ToricInput n} {φ : RealSpace n → ℝ}

private theorem euclideanRadius_pos {u : RealSpace n} (hu : u ≠ 0) :
    0 < Real.sqrt (realSquaredNorm u) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  rw [← e.apply_symm_apply u, realSquaredNorm_euclidean, Real.sqrt_sq (norm_nonneg _)]
  exact norm_pos_iff.mpr (by simpa [e] using hu)

/-- A maximizing vertex forces the actual gradient into its native open star. -/
theorem IsStronglyCompatibleEndPotential.gradient_mem_interior_rayStar
    (hφ : IsStronglyCompatibleEndPotential I φ) {u : RealSpace n} (hu : u ≠ 0)
    {a : Lattice n} (ha : a ∈ I.vertices)
    (hmax : pairing a u = supportHeight I u) :
    coordinateGradient φ u ∈ interior (rayStar I a) := by
  obtain ⟨c, hc, H, hH, hbounds⟩ := I.exists_supportHeight_linear_bounds
  have hq : 0 < supportHeight I u :=
    lt_of_lt_of_le (mul_pos hc (euclideanRadius_pos hu)) (hbounds u).1
  have hunit : supportHeight I ((supportHeight I u)⁻¹ • u) = 1 := by
    rw [I.supportHeight_smul_of_nonneg (inv_pos.mpr hq).le]
    exact inv_mul_cancel₀ hq.ne'
  have hfacet : (supportHeight I u)⁻¹ • u ∈ polarFacet I a := by
    refine ⟨?_, ?_⟩
    · change supportHeight I ((supportHeight I u)⁻¹ • u) ≤ 1
      exact hunit.le
    · rw [pairing_smul_real, hmax]
      exact inv_mul_cancel₀ hq.ne'
  have hstar := hφ.facet_star a ha hfacet
  rw [coordinateGradient_smul_of_homogeneous_two hφ.homogeneous
    (fun x hx => (hφ.smooth x hx).differentiableAt (by simp)) hu (inv_pos.mpr hq)] at hstar
  exact (I.smul_mem_interior_rayStar_iff a _ (inv_pos.mpr hq)).mp hstar

/-- The support deficit is strictly positive for a vertex outside a cone
containing the gradient at a nonzero point. -/
theorem IsStronglyCompatibleEndPotential.pairing_lt_supportHeight
    (hφ : IsStronglyCompatibleEndPotential I φ) {σ : Set (RealSpace n)}
    (hσ : σ ∈ faceFan I) {u : RealSpace n} (hu : u ≠ 0)
    (hgrad : coordinateGradient φ u ∈ σ) {a : Lattice n}
    (ha : a ∈ I.vertices) (haσ : latticeReal a ∉ σ) :
    pairing a u < supportHeight I u := by
  refine lt_of_le_of_ne (I.pairing_le_supportHeight u ⟨a, ha⟩) ?_
  intro heq
  have hstar := hφ.gradient_mem_interior_rayStar hu ha heq
  exact haσ ((I.mem_interior_rayStar_iff a _).mp hstar σ hσ hgrad)

/-- For one fixed cone and outside vertex, the unit-sphere deficit has a
strictly positive lower bound. The restricted sphere may be empty. -/
theorem IsStronglyCompatibleEndPotential.exists_unit_pairingGap
    (hφ : IsStronglyCompatibleEndPotential I φ) {σ : Set (RealSpace n)}
    (hσ : σ ∈ faceFan I) {a : Lattice n} (ha : a ∈ I.vertices)
    (haσ : latticeReal a ∉ σ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 →
      coordinateGradient φ ((EuclideanSpace.equiv (Fin n) ℝ) x) ∈ σ →
      δ ≤ supportHeight I ((EuclideanSpace.equiv (Fin n) ℝ) x) -
        pairing a ((EuclideanSpace.equiv (Fin n) ℝ) x) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  let K := S ∩ (coordinateGradient φ ∘ e) ⁻¹' σ
  have hnonzero : ∀ x ∈ S, e x ≠ 0 := by
    intro x hx
    have hxnorm : ‖x‖ = 1 := by simpa [S, Metric.mem_sphere, dist_zero_right] using hx
    have hxzero : x ≠ 0 := by intro h; simp [h] at hxnorm
    simpa [e] using hxzero
  have hgrad : ContinuousOn (coordinateGradient φ ∘ e) S := by
    intro x hx
    exact ((continuousAt_coordinateGradient (hφ.smooth _ (hnonzero x hx))).comp
      e.continuous.continuousAt).continuousWithinAt
  have hclosed : IsClosed K :=
    hgrad.preimage_isClosed_of_isClosed Metric.isClosed_sphere (I.isClosed_of_mem_faceFan hσ)
  have hcompact : IsCompact K :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).of_isClosed_subset hclosed
      inter_subset_left
  have hcont : ContinuousOn (fun x => supportHeight I (e x) - pairing a (e x)) K := by
    apply ((I.supportHeight_continuous.comp e.continuous).sub
      ((pairingCLM a).continuous.comp e.continuous)).continuousOn.congr
    intro x hx
    simp only [Pi.sub_apply, Function.comp_apply, pairingCLM_apply]
  obtain ⟨δ, hδ, hbound⟩ := hcompact.exists_forall_le' hcont (a := 0) (by
    intro x hx
    exact sub_pos.mpr (hφ.pairing_lt_supportHeight hσ (hnonzero x hx.1) hx.2 ha haσ))
  refine ⟨δ, hδ, ?_⟩
  intro x hx hσx
  exact hbound x ⟨by simpa [S, Metric.mem_sphere, dist_zero_right] using hx, hσx⟩

/-- One strictly positive Euclidean linear gap works for every native fan
cone and every vertex outside it. This includes the zero cone and points
where the gradient vanishes, so it implies `eq:phasegap` directly. -/
theorem IsStronglyCompatibleEndPotential.uniform_angularExclusionGap
    (hφ : IsStronglyCompatibleEndPotential I φ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ σ ∈ faceFan I, ∀ u : RealSpace n,
      coordinateGradient φ u ∈ σ → ∀ a ∈ I.vertices, latticeReal a ∉ σ →
      δ₀ * Real.sqrt (realSquaredNorm u) ≤ supportHeight I u - pairing a u := by
  classical
  let : Fintype {σ // σ ∈ faceFan I} := I.finite_faceFan.fintype
  let : Nonempty {σ // σ ∈ faceFan I} := ⟨⟨{0}, Or.inl rfl⟩⟩
  let : Nonempty {a // a ∈ I.vertices} :=
    ⟨⟨I.vertices_nonempty.choose, I.vertices_nonempty.choose_spec⟩⟩
  let C := {σ // σ ∈ faceFan I} × {a // a ∈ I.vertices}
  have hpair : ∀ i : C, ∃ δ : ℝ, 0 < δ ∧
      ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 →
        coordinateGradient φ ((EuclideanSpace.equiv (Fin n) ℝ) x) ∈ i.1.val →
        latticeReal i.2.val ∉ i.1.val →
        δ ≤ supportHeight I ((EuclideanSpace.equiv (Fin n) ℝ) x) -
          pairing i.2.val ((EuclideanSpace.equiv (Fin n) ℝ) x) := by
    intro i
    by_cases haσ : latticeReal i.2.val ∈ i.1.val
    · exact ⟨1, zero_lt_one, fun _ _ _ hout => False.elim (hout haσ)⟩
    · obtain ⟨δ, hδ, hbound⟩ := hφ.exists_unit_pairingGap i.1.property i.2.property haσ
      exact ⟨δ, hδ, fun x hx hg _ => hbound x hx hg⟩
  choose d hdpos hd using hpair
  obtain ⟨i₀, _, hmin⟩ := Finset.univ.exists_min_image d Finset.univ_nonempty
  refine ⟨d i₀, hdpos i₀, ?_⟩
  intro σ hσ u hgrad a ha haσ
  by_cases hu : u = 0
  · subst u
    simp [I.supportHeight_zero, pairing, realSquaredNorm]
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let r := ‖e.symm u‖
  have hr : 0 < r := norm_pos_iff.mpr (by simpa [e] using hu)
  let x : EuclideanSpace ℝ (Fin n) := r⁻¹ • e.symm u
  have hx : ‖x‖ = 1 := by
    dsimp [x]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact inv_mul_cancel₀ hr.ne'
  have hex : e x = r⁻¹ • u := by simp [x]
  have hxgrad : coordinateGradient φ (e x) ∈ σ := by
    rw [hex, coordinateGradient_smul_of_homogeneous_two hφ.homogeneous
      (fun z hz => (hφ.smooth z hz).differentiableAt (by simp)) hu (inv_pos.mpr hr)]
    exact I.smul_mem_of_mem_faceFan hσ hgrad (inv_pos.mpr hr).le
  have hbound := (hmin ⟨⟨σ, hσ⟩, ⟨a, ha⟩⟩ (Finset.mem_univ _)).trans
    (hd ⟨⟨σ, hσ⟩, ⟨a, ha⟩⟩ x hx hxgrad haσ)
  change d i₀ ≤ supportHeight I (e x) - pairing a (e x) at hbound
  rw [hex, I.supportHeight_smul_of_nonneg (inv_pos.mpr hr).le,
    pairing_smul_real, ← mul_sub] at hbound
  have hradius : Real.sqrt (realSquaredNorm u) = r := by
    rw [← e.apply_symm_apply u, realSquaredNorm_euclidean, Real.sqrt_sq (norm_nonneg _)]
  rw [hradius]
  calc
    d i₀ * r ≤ (r⁻¹ * (supportHeight I u - pairing a u)) * r :=
      mul_le_mul_of_nonneg_right hbound hr.le
    _ = supportHeight I u - pairing a u := by field_simp

end FsFltz
