import FsFltz.Analysis.TailoringExhaustionDomain
import FsFltz.Geometry.RankTwoPrimitiveFamily
import FsFltz.Geometry.FamilyCompletionAssembly

/-!
# The actual fixed outer domain and its smooth tailoring completions

Source: `geometric-part-fsf-proof.tex`, `subsec:finite`, lines 1182–1196,
and `lem:grading`, lines 1994–2001. One literal potential sublevel and its
boundary presentation precede all tailoring parameters and nonnegative base
coefficients. The actual primitives construct smooth localized completions.
No global ambient completion marking onto the tailored LG space is asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}

/-- The actual tailoring primitive has a jointly smooth all-real extension. -/
theorem isSmoothFormFamily_tailoringPrimitive (I : ToricInput n) (β K : ℝ)
    {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    (lgManifold n).IsSmoothFormFamily (fun s =>
      (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K) := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  let f := tailoringFamily I β 0
  let g := tailoringFamily I β 1 - tailoringFamily I β 0
  have he (s : ℝ) : tailoringFamily I β s = f + s • g := by
    funext y
    simp only [f, g, tailoringFamily, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_zero]
    ring
  simp_rw [he]
  exact (lgManifold n).isSmoothFormFamily_rankTwoPrimitive_affine
    (contMDiff_tailoringFamily_lgManifold I β 0)
    ((contMDiff_tailoringFamily_lgManifold I β 1).sub
      (contMDiff_tailoringFamily_lgManifold I β 0))
    (isSmoothForm_lambdaPotentialForm hφ) K

/-- A single literal outer carrier supports every tailoring parameter and
nonnegative coefficient. For each coefficient the actual primitive family
constructs both compact and completed smooth presentations. -/
theorem tailoringFamily_exists_uniform_fixedOuter_liouvilleFamily
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
      ∃ (E : CompactDomain (2 * n))
        (L : Parameter → (K : ℝ) → 0 ≤ K → LiouvilleStructure E),
        E.extension = lgManifold n ∧
        HEq E.carrier {y : LGSpace n | 2 * φ y.1 ≤ D ^ 2 * β ^ 2} ∧
        E.carrier.Nonempty ∧
        (∀ s K hK, HEq (L s K hK).primitive
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
            (tailoringFamily I β s.val) K)) ∧
        ∀ K hK, E.extension.IsSmoothIntervalFormFamily (fun s => (L s K hK).primitive) ∧
          Nonempty (LocalizedCompletionFamily E (fun s => L s K hK)) := by
  obtain ⟨B, hB, hdata⟩ := tailoringFamily_exists_uniform_potential_sublevel_data
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hREnd heq hD
  refine ⟨B, hB, ?_⟩
  intro β hβ
  obtain ⟨hcompact, hnonempty, hfamily⟩ := hdata β hβ
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  let ρ : LGSpace n → ℝ := fun y => φ y.1 - D ^ 2 * β ^ 2 / 2
  have hρ : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ ρ :=
    (contMDiff_potentialValue hφ).sub contMDiff_const
  let α := fun (s K : ℝ) =>
    (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K
  have hα (s K : ℝ) : (lgManifold n).IsSmoothForm (α s K) :=
    (lgManifold n).isSmoothForm_rankTwoPrimitive (isSmoothForm_lambdaPotentialForm hφ)
      (contMDiff_tailoringFamily_lgManifold I β s) K
  have hr := regular_zero_of_scalarDerivative_pos (lgManifold n) ρ
    ((lgManifold n).liouvilleVector (α 0 0))
    (hfamily 0 (by constructor <;> norm_num) 0 le_rfl).2
  let E := regularSublevelCompactDomain (lgManifold n) ρ hρ hcompact hr
  let L : Parameter → (K : ℝ) → 0 ≤ K → LiouvilleStructure E := fun s K hK =>
    (regularSublevelLiouvilleDomain (lgManifold n) ρ hρ hcompact
      (α s.val K) (hα s.val K) (hfamily s.val s.property K hK).1
      (hfamily s.val s.property K hK).2).liouville
  refine ⟨E, L, rfl, ?_, hnonempty, fun _ _ _ => HEq.rfl, ?_⟩
  · apply heq_of_eq
    ext y
    change (φ y.1 - D ^ 2 * β ^ 2 / 2 ≤ 0) ↔ (2 * φ y.1 ≤ D ^ 2 * β ^ 2)
    constructor <;> intro hy <;> linarith only [hy]
  · intro K hK
    have hsm : E.extension.IsSmoothIntervalFormFamily (fun s => (L s K hK).primitive) :=
      ⟨fun s => α s K, isSmoothFormFamily_tailoringPrimitive I β K hφ, fun _ => rfl⟩
    exact ⟨hsm, E.exists_smooth_localizedCompletionFamily_of_liouvilleFamily
      (fun s => L s K hK) hsm⟩

end FsFltz
