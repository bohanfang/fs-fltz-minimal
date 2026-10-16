import FsFltz.Geometry.TailoringRoundedDomain
import FsFltz.Geometry.TailoringMarkedLevelFamily

/-!
# Joint equations and compact total spaces for rounded tailoring domains

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009,
and `eq:normalizedrounding`, lines 1254–1282. The scalar and its literal
sublevel are retained; no smooth bundle or compatible ribbon lift is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry
variable {n : ℕ}

/-- The prescribed rounded defining equation is jointly smooth through
both parameter endpoints, including its literal normalization factor. -/
theorem contMDiff_tailoringRoundedDefiningFunction_joint (I : ToricInput n)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (β R A : ℝ) (m : RoundingChoice) :
    letI : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × LGSpace n => tailoringRoundedDefiningFunction I φ β p.1 R A m p.2) := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hnorm : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × LGSpace n => Complex.normSq (tailoringFamily I β p.1 p.2)) := by
    simpa only [Complex.normSq_eq_norm_sq, Function.comp_def] using
      (contDiff_norm_sq ℝ).contMDiff.comp (contMDiff_tailoringFamily_native_joint I β)
  exact m.profile.smooth.contMDiff.comp
    ((((contMDiff_potentialValue hφ).comp contMDiff_snd).sub contMDiff_const).prodMk_space
      (contMDiff_const.mul (hnorm.sub contMDiff_const)))

/-- The whole rounded domain family is compact over the closed parameter
interval. The smooth maximum's lower bound places it in one compact
potential cylinder. -/
theorem isCompact_tailoringRoundedDomain_totalSpace (I : ToricInput n)
    {φ φEnd : RealSpace n → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    (β R A : ℝ) (m : RoundingChoice) :
    IsCompact {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
      p.2 ∈ tailoringRoundedDomain I φ β p.1 R A m} := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hbase := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod
    (isCompact_potential_sublevel hφ hEnd1 hEnd hhom hc hlower hL hend A)
  have hq := (contMDiff_tailoringRoundedDefiningFunction_joint I hφ β R A m).continuous
  have hclosed : IsClosed {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
      p.2 ∈ tailoringRoundedDomain I φ β p.1 R A m} :=
    (isClosed_Icc.preimage continuous_fst).inter (isClosed_le hq continuous_const)
  apply hbase.of_isClosed_subset hclosed
  intro p hp
  refine ⟨hp.1, ?_⟩
  have h := (le_max_left (φ p.2.1 - A)
    (R ^ 2 * (Complex.normSq (tailoringFamily I β p.1 p.2) - 1))).trans
      ((m.profile.lower _).trans hp.2)
  exact sub_nonpos.mp h

/-- A regular point of the literal rounded equation has a jointly smooth
local parameter motion preserving that equation. The concrete family below
will discharge regularity from its actual outward Liouville derivative. -/
theorem tailoringRounded_exists_local_motion_of_regular (I : ToricInput n)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (β R A : ℝ) (m : RoundingChoice) (s : ℝ) (y : (lgManifold n).Point)
    (hregular : letI : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
      mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
      (tailoringRoundedDefiningFunction I φ β s R A m) y ≠ 0) :
    letI : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
    letI : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
      inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
    ∃ (O : Set (ℝ × (ℝ × LGSpace n))) (Ψ : ℝ × (ℝ × LGSpace n) → ℝ × LGSpace n),
      IsOpen O ∧ (0, (s, y)) ∈ O ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × Model (2 * n)))
        𝓘(ℝ, ℝ × Model (2 * n)) ∞ Ψ O ∧
      (∀ p, (0, p) ∈ O → Ψ (0, p) = p) ∧
      ∀ p ∈ O, (Ψ p).1 = p.2.1 + p.1 ∧
        tailoringRoundedDefiningFunction I φ β (Ψ p).1 R A m (Ψ p).2 =
          tailoringRoundedDefiningFunction I φ β p.2.1 R A m p.2.2 := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  let : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth
  have hsurj : Function.Surjective (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
      (tailoringRoundedDefiningFunction I φ β s R A m) y) := by
    apply LinearMap.surjective (f := (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
      (tailoringRoundedDefiningFunction I φ β s R A m) y).toLinearMap)
    intro hz
    exact hregular (ContinuousLinearMap.coe_injective hz)
  exact exists_parameter_level_local_motion
    (contMDiff_tailoringRoundedDefiningFunction_joint I hφ β R A m) hsurj

/-- The actual rounded boundary has local smooth motions, with regularity
proved from the finite-input outwardness estimate uniformly in the allowed
rounding profile. These motions preserve the literal defining equation. -/
theorem tailoringFamily_exists_uniform_rounded_boundary_motion
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
      ∃ Kstar : ℝ, 0 < Kstar ∧ ∀ R : ℝ, 0 < R →
      ∀ Aminus : ℝ, Aminus < D ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < D ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ y : LGSpace n,
      tailoringRoundedDefiningFunction I φ β s R (D ^ 2 * β ^ 2 / 2) m y = 0 →
      letI : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
      letI : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
        inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
      ∃ (O : Set (ℝ × (ℝ × LGSpace n))) (Ψ : ℝ × (ℝ × LGSpace n) → ℝ × LGSpace n),
        IsOpen O ∧ (0, (s, y)) ∈ O ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × Model (2 * n)))
          𝓘(ℝ, ℝ × Model (2 * n)) ∞ Ψ O ∧
        (∀ p, (0, p) ∈ O → Ψ (0, p) = p) ∧
        ∀ p ∈ O, (Ψ p).1 = p.2.1 + p.1 ∧
          tailoringRoundedDefiningFunction I φ β (Ψ p).1 R (D ^ 2 * β ^ 2 / 2) m (Ψ p).2 =
            tailoringRoundedDefiningFunction I φ β p.2.1 R (D ^ 2 * β ^ 2 / 2) m p.2.2 := by
  obtain ⟨β₀, hβ₀, hout⟩ := tailoringFamily_exists_uniform_rounded_outwardness
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hREnd heq hD
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ
  obtain ⟨Kstar, hKstar, hout⟩ := hout β hβ
  refine ⟨Kstar, hKstar, ?_⟩
  intro R hR Aminus hgap
  obtain ⟨δ, hδ, hδgap, hout⟩ := hout R hR Aminus hgap
  refine ⟨δ, hδ, hδgap, ?_⟩
  intro m hm hmd s hs y hy
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hpot := (tailoringRoundedDomain_subset I φ β s (D ^ 2 * β ^ 2 / 2) hR m
    (show y ∈ tailoringRoundedDomain I φ β s R (D ^ 2 * β ^ 2 / 2) m from hy.le)).1
  have hpos := hout m hm hmd Kstar le_rfl s hs y hpot hy.ge
  apply tailoringRounded_exists_local_motion_of_regular I hφ β R (D ^ 2 * β ^ 2 / 2) m s y
  intro hz
  have hzero : (lgManifold n).scalarDerivative
      (tailoringRoundedDefiningFunction I φ β s R (D ^ 2 * β ^ 2 / 2) m) y
      ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) (tailoringFamily I β s) Kstar) y) = 0 := by
    change (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
      (tailoringRoundedDefiningFunction I φ β s R (D ^ 2 * β ^ 2 / 2) m) y) _ = 0
    rw [hz]
    rfl
  exact (ne_of_gt hpos) hzero

end FsFltz
