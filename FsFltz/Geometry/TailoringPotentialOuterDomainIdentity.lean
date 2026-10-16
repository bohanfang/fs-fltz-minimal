import FsFltz.Geometry.TailoringRoundedAbsorption

/-!
# The fixed native domain of the tailoring outer family

Source: `geometric-part-fsf-proof.tex`, common marking, lines 1270–1303.
Only the primitive varies with the parameter: the regular potential sublevel
has the same scalar function, native extension, and boundary presentation.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry

/-- The domain projection retains the original scalar regular sublevel. -/
theorem regularSublevelLiouvilleDomain_domain {d : ℕ}
    (M : SmoothManifold d) (ρ : M.Point → ℝ)
    (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    (hc : IsCompact {x : M.Point | ρ x ≤ 0})
    (α : M.Form 1) (ha : M.IsSmoothForm α)
    (hω : M.IsSymplecticOn (M.exteriorDerivative α) univ)
    (ho : ∀ x, ρ x = 0 → 0 < M.scalarDerivative ρ x (M.liouvilleVector α x)) :
    (regularSublevelLiouvilleDomain M ρ hρ hc α ha hω ho).domain =
      regularSublevelCompactDomain M ρ hρ hc
        (regular_zero_of_scalarDerivative_pos M ρ (M.liouvilleVector α) ho) := rfl

/-- Abstract regular sublevel domains do not depend on the primitive used
to prove boundary regularity. -/
theorem regularSublevelLiouvilleDomain_domain_eq {d : ℕ}
    (M : SmoothManifold d) (ρ : M.Point → ℝ)
    (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    (hc₀ hc₁ : IsCompact {x : M.Point | ρ x ≤ 0})
    (α₀ α₁ : M.Form 1) (ha₀ : M.IsSmoothForm α₀) (ha₁ : M.IsSmoothForm α₁)
    (hω₀ : M.IsSymplecticOn (M.exteriorDerivative α₀) univ)
    (hω₁ : M.IsSymplecticOn (M.exteriorDerivative α₁) univ)
    (ho₀ : ∀ x, ρ x = 0 → 0 < M.scalarDerivative ρ x (M.liouvilleVector α₀ x))
    (ho₁ : ∀ x, ρ x = 0 → 0 < M.scalarDerivative ρ x (M.liouvilleVector α₁ x)) :
    (regularSublevelLiouvilleDomain M ρ hρ hc₁ α₁ ha₁ hω₁ ho₁).domain =
      (regularSublevelLiouvilleDomain M ρ hρ hc₀ α₀ ha₀ hω₀ ho₀).domain := by
  calc
    _ = regularSublevelCompactDomain M ρ hρ hc₁
        (regular_zero_of_scalarDerivative_pos M ρ (M.liouvilleVector α₁) ho₁) :=
      regularSublevelLiouvilleDomain_domain M ρ hρ hc₁ α₁ ha₁ hω₁ ho₁
    _ = regularSublevelCompactDomain M ρ hρ hc₀
        (regular_zero_of_scalarDerivative_pos M ρ (M.liouvilleVector α₀) ho₀) := rfl
    _ = _ := (regularSublevelLiouvilleDomain_domain M ρ hρ hc₀ α₀ ha₀ hω₀ ho₀).symm

variable {n : ℕ}
local instance outerIdentityLGCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts

/-- Project the actual outer domain to its explicit scalar sublevel once. -/
theorem tailoringPotentialOuterDomain_domain
    (I : ToricInput n) {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (β s K A : ℝ) (hc : IsCompact {y : LGSpace n | φ y.1 - A ≤ 0})
    (hω : (lgManifold n).IsSymplecticOn ((lgManifold n).exteriorDerivative
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K)) univ)
    (ho : ∀ y : (lgManifold n).Point, φ y.1 - A = 0 →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1 - A) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β s) K) y)) :
    (tailoringPotentialOuterDomain I hφ β s K A hc hω ho).domain =
      regularSublevelCompactDomain (lgManifold n) (fun y => φ y.1 - A)
        ((contMDiff_potentialValue hφ).sub contMDiff_const) hc
        (regular_zero_of_scalarDerivative_pos (lgManifold n) (fun y => φ y.1 - A)
          ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
            (lambdaPotentialForm φ) (tailoringFamily I β s) K)) ho) :=
  regularSublevelLiouvilleDomain_domain _ _ _ hc _ _ hω ho

/-- The compact domain is independent of the tailoring parameter.
Proof irrelevance identifies its scalar regularity witnesses. -/
theorem tailoringPotentialOuterDomain_domain_eq
    (I : ToricInput n) {φ : RealSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (β s t K A : ℝ)
    (hc₀ hc₁ : IsCompact {y : LGSpace n | φ y.1 - A ≤ 0})
    (hω₀ : (lgManifold n).IsSymplecticOn ((lgManifold n).exteriorDerivative
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K)) univ)
    (hω₁ : (lgManifold n).IsSymplecticOn ((lgManifold n).exteriorDerivative
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β t) K)) univ)
    (ho₀ : ∀ y : (lgManifold n).Point, φ y.1 - A = 0 →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1 - A) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β s) K) y))
    (ho₁ : ∀ y : (lgManifold n).Point, φ y.1 - A = 0 →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1 - A) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β t) K) y)) :
    (tailoringPotentialOuterDomain I hφ β t K A hc₁ hω₁ ho₁).domain =
      (tailoringPotentialOuterDomain I hφ β s K A hc₀ hω₀ ho₀).domain :=
  regularSublevelLiouvilleDomain_domain_eq _ _ _ hc₀ hc₁ _ _ _ _ hω₀ hω₁ ho₀ ho₁

/-- Explicit transport along a native-domain equality reassembles exactly
the original Liouville domain, without normalizing its construction. -/
theorem LiouvilleDomain.transport_liouville_eq {d : ℕ}
    (D : LiouvilleDomain d) (E : CompactDomain d) (h : D.domain = E) :
    (⟨E, h ▸ D.liouville⟩ : LiouvilleDomain d) = D := by
  cases h
  rfl

end FsFltz
