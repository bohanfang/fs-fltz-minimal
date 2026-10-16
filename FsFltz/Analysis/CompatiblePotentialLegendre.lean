import FsFltz.Analysis.CompatiblePotentialExistence
import FsFltz.Analysis.CoordinateStrongConvexLegendre

/-!
# Compatible potentials and their actual Legendre maps

Source: `geometric-part-fsf-proof.tex`, `lem:potential`, lines 626–643.
The native coordinate gradient is used throughout. The global extension
agrees literally with the homogeneous potential outside a Euclidean ball.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace FsFltz

variable {n : ℕ}

/-- Transport the smooth convex extension through the canonical fixed-basis
Euclidean coordinates, retaining its actual native gradient diffeomorphism. -/
theorem exists_native_smooth_extension_with_legendre
    {f : RealSpace n → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : Continuous f) (hf0 : f 0 = 0)
    (hfs : ∀ x ≠ 0, ContDiffAt ℝ ∞ f x)
    (hconv : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n) =>
      f ((EuclideanSpace.equiv (Fin n) ℝ) x) - δ * ‖x‖ ^ 2))
    (hlower : ∀ x : EuclideanSpace ℝ (Fin n), δ * ‖x‖ ^ 2 ≤
      f ((EuclideanSpace.equiv (Fin n) ℝ) x)) :
    ∃ g : RealSpace n → ℝ, ContDiff ℝ ∞ g ∧
      (∀ x v : EuclideanSpace ℝ (Fin n), δ * ‖v‖ ^ 2 ≤ inner ℝ
        ((fderiv ℝ (gradient (g ∘ EuclideanSpace.equiv (Fin n) ℝ)) x) v) v) ∧
      (∀ᶠ x in 𝓝 (0 : RealSpace n), g x = (δ / 2) * realSquaredNorm x + 1) ∧
      (∃ R > 0, ∀ x, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x‖ → g x = f x) ∧
      ∃ H : RealSpace n ≃ₜ RealSpace n,
        (∀ x, H x = coordinateGradient g x) ∧ ContDiff ℝ ∞ H.symm := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hconv' : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n) =>
      (f ∘ e) x - (δ / 2) * ‖x‖ ^ 2) := by
    have hn : ConvexOn ℝ (univ : Set (EuclideanSpace ℝ (Fin n))) (fun x => ‖x‖ ^ 2) :=
      (convexOn_norm convex_univ).pow (fun _ _ => norm_nonneg _) 2
    convert hconv.add (hn.smul (show 0 ≤ δ / 2 by positivity)) using 1
    ext x
    simp only [Pi.add_apply, smul_eq_mul, Function.comp_apply]
    ring
  obtain ⟨G, hGs, hGb, hG0, ⟨R, hR, hGR⟩, HG, hHG, hHGinv⟩ :=
    exists_smooth_extension_with_legendre (a := δ / 2) (c := δ / 2) (d := δ)
      (by positivity) le_rfl (by linarith) (hf.comp e.continuous)
      (by simpa using hf0)
      (fun x hx => (hfs (e x) (by simpa [e] using hx)).comp x e.contDiff.contDiffAt)
      hconv' hlower
  let g := G ∘ e.symm
  let H := e.symm.toHomeomorph.trans (HG.trans e.toHomeomorph)
  have hgs : ContDiff ℝ ∞ g := hGs.comp e.symm.contDiff
  have hge : g ∘ e = G := by ext x; simp [g]
  have hgb (x v : EuclideanSpace ℝ (Fin n)) : δ * ‖v‖ ^ 2 ≤ inner ℝ
      ((fderiv ℝ (gradient (g ∘ e)) x) v) v := by
    rw [hge]
    convert hGb x v using 1
    ring
  refine ⟨g, hgs, hgb, ?_, ⟨R, hR, ?_⟩, H, ?_, ?_⟩
  · have h := (e.symm.continuous.tendsto 0).eventually (by simpa using hG0)
    filter_upwards [h] with x hx
    have hn : realSquaredNorm x = ‖e.symm x‖ ^ 2 := by
      have h := realSquaredNorm_euclidean (e.symm x)
      change realSquaredNorm (e (e.symm x)) = _ at h
      rwa [e.apply_symm_apply] at h
    change G (e.symm x) = _
    rwa [← hn] at hx
  · intro x hx
    simpa [g] using hGR (e.symm x) hx
  · intro x
    have he := coordinateGradient_eq_euclidean_gradient (hgs.differentiable (by simp)) x
    change coordinateGradient g x = e (gradient (g ∘ e) (e.symm x)) at he
    rw [hge] at he
    change e (HG (e.symm x)) = coordinateGradient g x
    rw [hHG]
    exact he.symm
  · exact e.contDiff.comp (hHGinv.comp e.symm.contDiff)

/-- The full potential lemma: a strongly compatible homogeneous end, a global
smooth strictly convex extension, and both literal Legendre maps with smooth
inverses on their stated domains. No geometric comparison data is assumed. -/
theorem ToricInput.exists_compatiblePotential_with_legendre (I : ToricInput n) :
    ∃ φEnd φ : RealSpace n → ℝ,
      IsStronglyCompatibleEndPotential I φEnd ∧ ContDiff ℝ 1 φEnd ∧ φEnd 0 = 0 ∧
      ContDiff ℝ ∞ φ ∧
      (∀ x v : EuclideanSpace ℝ (Fin n), v ≠ 0 → 0 < inner ℝ
        ((fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) x) v) v) ∧
      (∃ a > 0, ∀ᶠ x in 𝓝 (0 : RealSpace n), φ x = a * realSquaredNorm x + 1) ∧
      (∃ R > 0, ∀ x, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x‖ → φ x = φEnd x) ∧
      ∃ ΦEnd Φ : RealSpace n ≃ₜ RealSpace n,
        (∀ x, ΦEnd x = coordinateGradient φEnd x) ∧ ΦEnd 0 = 0 ∧
        ContDiffOn ℝ ∞ ΦEnd ({0}ᶜ : Set (RealSpace n)) ∧
        ContDiffOn ℝ ∞ ΦEnd.symm ({0}ᶜ : Set (RealSpace n)) ∧
        (∀ x, Φ x = coordinateGradient φ x) ∧ ContDiff ℝ ∞ Φ ∧
        ContDiff ℝ ∞ Φ.symm := by
  obtain ⟨φEnd, hstrong, hφ1, hφ0, δ, hδ, hconv, hlower, hbound⟩ :=
    I.exists_stronglyCompatibleEndPotential
  obtain ⟨φ, hφs, hφb, hφnear, hφend, Φ, hΦ, hΦinv⟩ :=
    exists_native_smooth_extension_with_legendre hδ hφ1.continuous hφ0
      hstrong.smooth hconv hlower
  have hgrad0 : coordinateGradient φEnd 0 = 0 := by
    have hm : IsLocalMin φEnd 0 := Filter.Eventually.of_forall fun x => by
      rw [hφ0]
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        (mul_nonneg hδ.le (sq_nonneg _)).trans (hlower
          ((EuclideanSpace.equiv (Fin n) ℝ).symm x))
    ext j
    simp [coordinateGradient, hm.fderiv_eq_zero]
  let ΦEnd := strongConvexCoordinateGradientHomeomorph hφ1 hδ hconv hlower
  refine ⟨φEnd, φ, hstrong, hφ1, hφ0, hφs, ?_, ⟨δ / 2, by positivity, hφnear⟩,
    hφend, ΦEnd, Φ, fun x => strongConvexCoordinateGradientHomeomorph_apply
      hφ1 hδ hconv hlower x, ?_, ?_, ?_, hΦ, ?_, hΦinv⟩
  · intro x v hv
    exact lt_of_lt_of_le (by positivity : 0 < δ * ‖v‖ ^ 2) (hφb x v)
  · simpa [ΦEnd] using hgrad0
  · exact contDiffOn_strongConvexCoordinateGradientHomeomorph hφ1 hδ hconv hlower hstrong.smooth
  · exact contDiffOn_symm_strongConvexCoordinateGradientHomeomorph hφ1 hδ hconv hlower hgrad0
      hstrong.smooth (show 0 < 2 * δ by positivity) hbound
  · have he : (Φ : RealSpace n → RealSpace n) = coordinateGradient φ := funext hΦ
    rw [he]
    exact contDiff_coordinateGradient hφs

end FsFltz
