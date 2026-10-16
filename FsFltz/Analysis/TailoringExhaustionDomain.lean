import FsFltz.Analysis.TailoringExhaustionPositivity
import FsFltz.Geometry.RegularSublevelDomain
import FsFltz.Geometry.PotentialFiberCompleteFlow

/-!
# Actual finite potential sublevels for the tailored primitive

Source: `geometric-part-fsf-proof.tex`, `subsec:finite`, lines 1182–1197.
The carrier is the literal compact potential sublevel; the native boundary
and Liouville structure are constructed by the regular-sublevel API.
No global ambient completion identification for the tailored primitive is
claimed. Compare `geoemtric-part-fsf.tex`, `thm:target`, lines 351–434,
and the pending geometric bridges in `sec:lean`, lines 802–824.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter
open scoped BigOperators ContDiff Manifold Topology

variable {n : ℕ}

/-- Compactness, nonemptiness, symplecticity and actual boundary derivatives
for the literal outer sublevel, before any presentation is selected. -/
theorem tailoringFamily_exists_uniform_potential_sublevel_data
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, φEnd (t • u) = t ^ 2 * φEnd u)
    {REnd : ℝ} (hREnd : 0 < REnd)
    (heq : ∀ u, REnd ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    {D : ℝ} (hD : 0 < D) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      IsCompact {y : LGSpace n | φ y.1 - D ^ 2 * β ^ 2 / 2 ≤ 0} ∧
      {y : LGSpace n | φ y.1 - D ^ 2 * β ^ 2 / 2 ≤ 0}.Nonempty ∧
      ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ K : ℝ, 0 ≤ K →
        (lgManifold n).IsSymplecticOn ((lgManifold n).exteriorDerivative
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
            (tailoringFamily I β s) K)) univ ∧
        ∀ y : (lgManifold n).Point, φ y.1 - D ^ 2 * β ^ 2 / 2 = 0 →
          0 < (lgManifold n).scalarDerivative
            (fun z => φ z.1 - D ^ 2 * β ^ 2 / 2) y
            ((lgManifold n).liouvilleVector
              ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
                (tailoringFamily I β s) K) y) := by
  obtain ⟨Bband, _hBband, hband⟩ := tailoringFamily_exists_uniform_finite_band_outwardness
    I hφ hc hU hlower hupper hEnd hhom hREnd heq hD hD
  obtain ⟨Bω, _hBω, hω⟩ := tailoringFamily_exists_uniform_symplectic I hφ hc hU hlower hupper
  obtain ⟨V, hV⟩ := (isCompact_phi0_sublevel (n := n) (REnd ^ 2 / 2) (by positivity)).bddAbove_image
    (hφ.continuous.comp continuous_fst).continuousOn
  let Bφ := (2 * max V 0 + 1) / D
  let β₀ := max 1 (max Bband (max Bω Bφ))
  refine ⟨β₀, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro β hβ
  have hβ₁ : 1 ≤ β := (le_max_left _ _).trans hβ
  have hβband : Bband ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβω : Bω ≤ β := (le_max_left _ _).trans
    ((le_max_right Bband _).trans ((le_max_right 1 _).trans hβ))
  have hβφ : Bφ ≤ β := (le_max_right _ _).trans
    ((le_max_right Bband _).trans ((le_max_right 1 _).trans hβ))
  have hDβ : 0 < D * β := mul_pos hD (lt_of_lt_of_le zero_lt_one hβ₁)
  have hlevel : V < D ^ 2 * β ^ 2 / 2 := by
    have hbound : 2 * max V 0 + 1 ≤ D * β := by
      have h := (div_le_iff₀ hD).mp hβφ
      simpa only [mul_comm] using h
    have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * max V 0 + 1) hbound 2
    nlinarith only [hsquare, le_max_left V 0, le_max_right V 0, sq_nonneg (max V 0)]
  let a := D ^ 2 * β ^ 2 / 2
  let ρ : LGSpace n → ℝ := fun y => φ y.1 - a
  let : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hρ : ContMDiff 𝓘(ℝ, Geometry.Model (2 * n)) 𝓘(ℝ, ℝ) ∞ ρ :=
    (contMDiff_potentialValue hφ).sub contMDiff_const
  have hcompact : IsCompact {y : LGSpace n | ρ y ≤ 0} := by
    have h := isCompact_potential_sublevel hφ hEnd1 hEnd hhom hc hlower hREnd heq a
    convert h using 1
    ext y
    simp only [ρ, Set.mem_ofPred_eq, sub_nonpos]
  refine ⟨hcompact, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := phi0_sublevel_nonempty (n := n) (REnd ^ 2 / 2) (by positivity)
    refine ⟨y, ?_⟩
    have hbound := hV (mem_image_of_mem (fun z : LGSpace n => φ z.1) hy)
    change φ y.1 ≤ V at hbound
    change φ y.1 - D ^ 2 * β ^ 2 / 2 ≤ 0
    linarith only [hbound, hlevel]
  · intro s hs K hK
    refine ⟨hω β hβω s hs K hK, ?_⟩
    let α := (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K
    have hout : ∀ y : (lgManifold n).Point, ρ y = 0 →
        0 < (lgManifold n).scalarDerivative ρ y ((lgManifold n).liouvilleVector α y) := by
      intro y hy
      have hyφ : φ y.1 = a := sub_eq_zero.mp hy
      have hyEnd : REnd < ‖(WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n))‖ := by
        by_contra h
        have hnorm : ‖(WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n))‖ ≤ REnd := le_of_not_gt h
        have hsq : realSquaredNorm y.1 ≤ REnd ^ 2 := by
          simpa [EuclideanSpace.norm_sq_eq, realSquaredNorm] using
            (sq_le_sq₀ (norm_nonneg _) hREnd.le).mpr hnorm
        have hmem : y ∈ {z : LGSpace n | phi0 z ≤ REnd ^ 2 / 2} := by
          change realSquaredNorm y.1 / 2 ≤ REnd ^ 2 / 2
          linarith
        have hbound := hV (mem_image_of_mem (fun z : LGSpace n => φ z.1) hmem)
        exact (not_le_of_gt hlevel) (by simpa only [hyφ] using hbound)
      obtain ⟨x, rfl⟩ := lgCover_surjective n y
      change φ x.1 = a at hyφ
      let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
      have he := metricRadialSq_potential_eq_two_mul hEnd1 hEnd hhom hc hlower hREnd heq x.1 hyEnd
      have hr : Real.sqrt (metricRadialSq H x.1) = D * β := by
        rw [he, hyφ]
        dsimp only [a]
        rw [show 2 * (D ^ 2 * β ^ 2 / 2) = (D * β) ^ 2 by ring,
          Real.sqrt_sq_eq_abs, abs_of_pos hDβ]
      have hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower (lgCover x)
      have hp := (hband β hβband s hs x (by rw [hr]) (by rw [hr]) hnd).2 K hK
      have hdρ : mfderiv 𝓘(ℝ, Geometry.Model (2 * n)) 𝓘(ℝ, ℝ) ρ (lgCover x) =
          mfderiv 𝓘(ℝ, Geometry.Model (2 * n)) 𝓘(ℝ, ℝ)
            (fun z : (lgManifold n).Point => φ z.1) (lgCover x) := by
        change mfderiv _ _ ((fun z : (lgManifold n).Point => φ z.1) - fun _ => a) (lgCover x) = _
        rw [mfderiv_sub ((contMDiff_potentialValue hφ).mdifferentiable (by simp) (lgCover x))
          mdifferentiableAt_const, mfderiv_const, sub_zero]
      unfold SmoothManifold.scalarDerivative
      rw [hdρ]
      exact hp
    exact hout

/-- The literal compact finite potential sublevel admits its native
Liouville domain structure for every later `K ≥ 0`. The actual ambient,
carrier, primitive, and field are retained in the conclusion. -/
theorem tailoringFamily_exists_uniform_potential_sublevel_domains
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, φEnd (t • u) = t ^ 2 * φEnd u)
    {REnd : ℝ} (hREnd : 0 < REnd)
    (heq : ∀ u, REnd ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    {D : ℝ} (hD : 0 < D) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∀ K : ℝ, 0 ≤ K → ∃ E : LiouvilleDomain (2 * n),
        E.domain.extension = lgManifold n ∧
        HEq E.domain.carrier {y : LGSpace n | 2 * φ y.1 ≤ D ^ 2 * β ^ 2} ∧
        E.domain.carrier.Nonempty ∧
        HEq E.liouville.primitive
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K) ∧
        HEq E.liouville.field ((lgManifold n).liouvilleVector
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K)) := by
  obtain ⟨B, hB, hdata⟩ := tailoringFamily_exists_uniform_potential_sublevel_data
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hREnd heq hD
  refine ⟨B, hB, ?_⟩
  intro β hβ s hs K hK
  obtain ⟨hcompact, hnonempty, hfamily⟩ := hdata β hβ
  obtain ⟨hω, hout⟩ := hfamily s hs K hK
  let : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  let ρ : LGSpace n → ℝ := fun y => φ y.1 - D ^ 2 * β ^ 2 / 2
  have hρ : ContMDiff 𝓘(ℝ, Geometry.Model (2 * n)) 𝓘(ℝ, ℝ) ∞ ρ :=
    (contMDiff_potentialValue hφ).sub contMDiff_const
  let α := (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K
  have hα : (lgManifold n).IsSmoothForm α :=
    (lgManifold n).isSmoothForm_rankTwoPrimitive (isSmoothForm_lambdaPotentialForm hφ)
      (contMDiff_tailoringFamily_lgManifold I β s) K
  let E := regularSublevelLiouvilleDomain (lgManifold n) ρ hρ hcompact α hα hω hout
  refine ⟨E, rfl, ?_, hnonempty, HEq.rfl, HEq.rfl⟩
  apply heq_of_eq
  ext y
  change (φ y.1 - D ^ 2 * β ^ 2 / 2 ≤ 0) ↔ (2 * φ y.1 ≤ D ^ 2 * β ^ 2)
  constructor <;> intro hy <;> linarith only [hy]

end FsFltz
