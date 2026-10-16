import FsFltz.Analysis.HomogeneousPotential
import FsFltz.Toric
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! # The tangent space of a transverse radial full-span section

Source: `geometric-part-fsf-proof.tex`, `lem:stable`, lines 1713–1718.
The Euler vector and the nonzero radial differential prove the tangent
range from the differentiated affine normalization and level equation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Set Function Filter
open scoped Topology ContDiff

variable {n : ℕ}

/-- Smoothness of both directions of the actual Legendre homeomorphism
constructs its native derivative equivalence. -/
theorem exists_fderiv_equiv_of_homeomorph (Φ : RealSpace n ≃ₜ RealSpace n)
    (u : RealSpace n) (hdΦ : DifferentiableAt ℝ Φ u)
    (hdinv : DifferentiableAt ℝ Φ.symm (Φ u)) :
    ∃ H : RealSpace n ≃L[ℝ] RealSpace n,
      (H : RealSpace n →L[ℝ] RealSpace n) = fderiv ℝ Φ u := by
  have hleftFun : (Φ.symm : RealSpace n → RealSpace n) ∘ Φ = id :=
    funext Φ.symm_apply_apply
  have hrightFun : (Φ : RealSpace n → RealSpace n) ∘ Φ.symm = id :=
    funext Φ.apply_symm_apply
  have hinvleft : fderiv ℝ Φ.symm (Φ u) ∘L fderiv ℝ Φ u =
      ContinuousLinearMap.id ℝ (RealSpace n) := by
    have hd := hdinv.hasFDerivAt.comp u hdΦ.hasFDerivAt
    rw [hleftFun] at hd
    exact hd.unique (hasFDerivAt_id (𝕜 := ℝ) u)
  have hinvright : fderiv ℝ Φ u ∘L fderiv ℝ Φ.symm (Φ u) =
      ContinuousLinearMap.id ℝ (RealSpace n) := by
    have hdΦ' : HasFDerivAt (Φ : RealSpace n → RealSpace n)
        (fderiv ℝ Φ u) (Φ.symm (Φ u)) := by
      rw [Homeomorph.symm_apply_apply]
      exact hdΦ.hasFDerivAt
    have hd := hdΦ'.comp (Φ u) hdinv.hasFDerivAt
    rw [hrightFun] at hd
    exact hd.unique (hasFDerivAt_id (𝕜 := ℝ) (Φ u))
  exact ContinuousLinearMap.IsInvertible.of_inverse hinvright hinvleft

/-- The two differentiated section equations determine the entire radial
tangent space; no dimension count or assumed tangent certificate is used. -/
theorem radial_fullSpan_tangent_range
    (V : Submodule ℝ (RealSpace n)) (ℓ : RealSpace n →L[ℝ] ℝ)
    (K : Submodule ℝ (RealSpace n)) (hK : K = V ⊓ ℓ.ker)
    (u p : RealSpace n) (H : RealSpace n ≃L[ℝ] RealSpace n)
    (hp : p ∈ V) (hℓ : ℓ p = 1) (hEuler : H u = p)
    (d : RealSpace n →L[ℝ] ℝ) (hd : d u ≠ 0)
    (L : K →L[ℝ] RealSpace n)
    (haffine : ∀ a : K, H (L a) - ℓ (H (L a)) • p = a)
    (hlevel : ∀ a : K, d (L a) = 0) :
    range L = {v | H v ∈ V ∧ d v = 0} := by
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨?_, hlevel a⟩
    have haV : (a : RealSpace n) ∈ V := by
      exact (show K ≤ V by rw [hK]; exact inf_le_left) a.property
    have he : H (L a) = (a : RealSpace n) + ℓ (H (L a)) • p :=
      eq_add_of_sub_eq (haffine a)
    rw [he]
    exact V.add_mem haV (V.smul_mem _ hp)
  · rintro ⟨hvV, hdv⟩
    let a : K := ⟨H v - ℓ (H v) • p, by
      rw [hK]
      refine ⟨V.sub_mem hvV (V.smul_mem _ hp), ?_⟩
      change ℓ (H v - ℓ (H v) • p) = 0
      simp [hℓ]⟩
    let c := ℓ (H v) - ℓ (H (L a))
    have hLa : H (L a) = (a : RealSpace n) + ℓ (H (L a)) • p :=
      eq_add_of_sub_eq (haffine a)
    have hHv : H (v - L a) = c • p := by
      rw [map_sub, hLa]
      change H v - ((H v - ℓ (H v) • p) + ℓ (H (L a)) • p) =
        (ℓ (H v) - ℓ (H (L a))) • p
      module
    have hv : v - L a = c • u := by
      apply H.injective
      rw [hHv, map_smul, hEuler]
    have hc : c = 0 := by
      have h := congrArg d hv
      simp only [map_sub, hdv, hlevel a, sub_self, map_smul, smul_eq_mul] at h
      exact (mul_eq_zero.mp h.symm).resolve_right hd
    refine ⟨a, ?_⟩
    rw [hc, zero_smul] at hv
    exact (sub_eq_zero.mp hv).symm

/-- Differentiating the actual normalization and level equations gives
the radial tangent range of a constructed section. -/
theorem fullSpan_section_fderiv_range
    (V : Submodule ℝ (RealSpace n)) (ℓ : RealSpace n →L[ℝ] ℝ)
    (K : Submodule ℝ (RealSpace n)) (hK : K = V ⊓ ℓ.ker)
    (u p : RealSpace n) (H : RealSpace n ≃L[ℝ] RealSpace n)
    (hp : p ∈ V) (hℓ : ℓ p = 1) (hEuler : H u = p)
    (Φ : RealSpace n → RealSpace n)
    (hΦ : HasFDerivAt Φ (H : RealSpace n →L[ℝ] RealSpace n) u)
    (ρ : RealSpace n → ℝ) (d : RealSpace n →L[ℝ] ℝ)
    (hρ : HasFDerivAt ρ d u) (hd : d u ≠ 0)
    (g : K → RealSpace n) (hg₀ : g 0 = u) (hg : DifferentiableAt ℝ g 0)
    (α : K → ℝ) (hα : DifferentiableAt ℝ α 0) (hα₀ : α 0 = 1)
    (haffine : ∀ᶠ q in 𝓝 (0 : K), Φ (g q) - ℓ (Φ (g q)) • p = α q • (q : RealSpace n))
    (hlevel : ∀ᶠ q in 𝓝 (0 : K), ρ (g q) = 1) :
    range (fderiv ℝ g 0) = {v | H v ∈ V ∧ d v = 0} := by
  apply radial_fullSpan_tangent_range V ℓ K hK u p H hp hℓ hEuler d hd
  · intro a
    have hΦg := (hg₀ ▸ hΦ).comp 0 hg.hasFDerivAt
    have hℓΦg := ℓ.hasFDerivAt.comp 0 hΦg
    have hder := hΦg.sub (hℓΦg.smul_const p)
    have he : (fun q : K => α q • (q : RealSpace n)) =ᶠ[𝓝 (0 : K)]
        (fun q => Φ (g q) - ℓ (Φ (g q)) • p) := by
      filter_upwards [haffine] with q hq
      exact hq.symm
    have hright : HasFDerivAt (fun q : K => α q • (q : RealSpace n)) K.subtypeL 0 := by
      have htemp := hα.hasFDerivAt.smul (K.subtypeL.hasFDerivAt (x := (0 : K)))
      simpa [hα₀] using htemp
    have hEq := (hder.congr_of_eventuallyEq he).unique hright
    have := congrArg (fun L : K →L[ℝ] RealSpace n => L a) hEq
    simpa only [sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.smulRight_apply,
      Submodule.subtypeL_apply] using this
  · intro a
    have hder := (hg₀ ▸ hρ).comp 0 hg.hasFDerivAt
    have he : (fun _ : K => (1 : ℝ)) =ᶠ[𝓝 (0 : K)] (fun q => ρ (g q)) := by
      filter_upwards [hlevel] with q hq
      exact hq.symm
    have hEq := (hder.congr_of_eventuallyEq he).unique (hasFDerivAt_const (1 : ℝ) (0 : K))
    have := congrArg (fun L : K →L[ℝ] ℝ => L a) hEq
    simpa only [ContinuousLinearMap.comp_apply, zero_apply] using this

/-- At every parameter point, translation and positive rescaling reduce
the actual degree-one radial graph to the normalized central calculation. -/
theorem fullSpan_section_fderiv_range_at
    (V : Submodule ℝ (RealSpace n)) (ℓ : RealSpace n →L[ℝ] ℝ)
    (K : Submodule ℝ (RealSpace n)) (hK : K = V ⊓ ℓ.ker)
    (p : RealSpace n) (hp : p ∈ V) (hℓ : ℓ p = 1)
    (B : Set K) (hB : IsOpen B) (q : K) (hq : q ∈ B)
    (g : K → RealSpace n) (hg : ∀ a ∈ B, DifferentiableAt ℝ g a)
    (α : K → ℝ) (hα : DifferentiableAt ℝ α q) (hαpos : 0 < α q)
    (Φ : RealSpace n → RealSpace n) (H : RealSpace n ≃L[ℝ] RealSpace n)
    (hΦ : HasFDerivAt Φ (H : RealSpace n →L[ℝ] RealSpace n) (g q))
    (hEuler : H (g q) = Φ (g q))
    (haffine : ∀ a ∈ B, Φ (g a) = α a • (p + a))
    (ρ : RealSpace n → ℝ) (d : RealSpace n →L[ℝ] ℝ)
    (hρ : HasFDerivAt ρ d (g q)) (hd : d (g q) ≠ 0)
    (hlevel : ∀ a ∈ B, ρ (g a) = 1) :
    range (fderiv ℝ g q) = {v | H v ∈ V ∧ d v = 0} := by
  let c := α q
  have hc : c ≠ 0 := hαpos.ne'
  let ℓ' := c⁻¹ • ℓ
  have hK' : K = V ⊓ ℓ'.ker := by
    rw [hK]
    congr 1
    ext v
    simp [ℓ', c, hαpos.ne', smul_eq_mul]
  let T : K → K := fun a => q + c⁻¹ • a
  let G := g ∘ T
  let A : K → ℝ := fun a => α (T a) * c⁻¹
  have hT₀ : T 0 = q := by simp [T]
  have hT : HasFDerivAt T (c⁻¹ • ContinuousLinearMap.id ℝ K) 0 := by
    exact ((hasFDerivAt_id (𝕜 := ℝ) (0 : K)).const_smul c⁻¹).const_add q
  have hG : HasFDerivAt G
      (fderiv ℝ g q ∘L (c⁻¹ • ContinuousLinearMap.id ℝ K)) 0 := by
    have htemp := (hT₀ ▸ (hg q hq).hasFDerivAt).comp 0 hT
    simpa only [hT₀] using htemp
  have hA : DifferentiableAt ℝ A 0 :=
    (((hT₀ ▸ hα).comp 0 hT.differentiableAt).mul_const c⁻¹)
  have hA₀ : A 0 = 1 := by
    simp only [A, hT₀]
    change c * c⁻¹ = 1
    exact mul_inv_cancel₀ hc
  have hpc : Φ (g q) ∈ V := by
    rw [haffine q hq]
    exact V.smul_mem _ (V.add_mem hp ((show K ≤ V by rw [hK]; exact inf_le_left) q.property))
  have hℓc : ℓ' (Φ (g q)) = 1 := by
    have hqℓ : ℓ (q : RealSpace n) = 0 := by
      exact (show K ≤ ℓ.ker by rw [hK]; exact inf_le_right) q.property
    rw [haffine q hq]
    simp [ℓ', map_smul, ℓ.map_add, hℓ, hqℓ, c, hc]
  have hnear : ∀ᶠ a in 𝓝 (0 : K), T a ∈ B :=
    hT.continuousAt.tendsto.eventually (by rw [hT₀]; exact hB.eventually_mem hq)
  have hAffine : ∀ᶠ a in 𝓝 (0 : K),
      Φ (G a) - ℓ' (Φ (G a)) • Φ (g q) = A a • (a : RealSpace n) := by
    filter_upwards [hnear] with a ha
    have haℓ : ℓ (a : RealSpace n) = 0 :=
      (show K ≤ ℓ.ker by rw [hK]; exact inf_le_right) a.property
    have hqℓ : ℓ (q : RealSpace n) = 0 :=
      (show K ≤ ℓ.ker by rw [hK]; exact inf_le_right) q.property
    have he : ℓ' (Φ (G a)) = c⁻¹ * α (T a) := by
      change (c⁻¹ • ℓ) (Φ (g (T a))) = _
      rw [haffine _ ha]
      simp only [smul_apply, map_smul, smul_eq_mul]
      have htℓ : ℓ ((T a : K) : RealSpace n) = 0 := by
        change ℓ (q + c⁻¹ • a) = 0
        simp [ℓ.map_add, map_smul, hqℓ, haℓ]
      rw [ℓ.map_add, hℓ, htℓ, add_zero, mul_one]
      ring
    rw [he, haffine q hq]
    change Φ (g (T a)) - (c⁻¹ * α (T a)) • (c • (p + q)) = _
    rw [haffine _ ha]
    change α (T a) • (p + (q + c⁻¹ • a)) -
      (c⁻¹ * α (T a)) • (c • (p + q)) = (α (T a) * c⁻¹) • (a : RealSpace n)
    rw [smul_smul]
    have hec : c⁻¹ * α (T a) * c = α (T a) := by field_simp
    rw [hec]
    module
  have hLevel : ∀ᶠ a in 𝓝 (0 : K), ρ (G a) = 1 := by
    filter_upwards [hnear] with a ha
    exact hlevel _ ha
  have hG₀ : G 0 = g q := by simp [G, hT₀]
  have hRange := fullSpan_section_fderiv_range V ℓ' K hK' (g q) (Φ (g q)) H
    hpc hℓc hEuler Φ hΦ ρ d hρ hd G hG₀ hG.differentiableAt A hA hA₀ hAffine hLevel
  rw [hG.fderiv] at hRange
  have hrange : range (fderiv ℝ g q ∘L (c⁻¹ • ContinuousLinearMap.id ℝ K)) =
      range (fderiv ℝ g q) := by
    ext v
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨c⁻¹ • a, ha⟩
    · rintro ⟨a, ha⟩
      refine ⟨c • a, ?_⟩
      simpa [ContinuousLinearMap.comp_apply, smul_smul, hc] using ha
  rwa [hrange] at hRange

end FsFltz
