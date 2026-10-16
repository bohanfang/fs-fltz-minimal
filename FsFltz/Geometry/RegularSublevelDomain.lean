import FsFltz.Geometry.RegularFiberManifold
import FsFltz.Geometry.RegularSublevelFrontier
import FsFltz.Geometry.SmoothLiouville

/-!
# Native compact and Liouville domains from regular scalar sublevels

Source: `geometric-part-fsf-proof.tex`, `prop:allinitial`, lines 909–920;
`geoemtric-part-fsf.tex`, `g:initial`, lines 363–384, and `sec:lean`,
lines 805–824. A compact regular scalar sublevel has a native smooth
boundary, constructed by the regular-level manifold theorem. The actual
scalar is its boundary defining function. A smooth symplectic primitive
with positive derivative along its actual Liouville field supplies the
native Liouville structure. No boundary atlas, embedding, domain or
Liouville structure is supplied as an input.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold

set_option backward.isDefEq.respectTransparency false in
private theorem exists_scalarRegularLevel_embedding {d : ℕ} (M : SmoothManifold d)
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    (hregular : ∀ x, ρ x = 0 → mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ x ≠ 0) :
    ∃ (B : SmoothManifold (d - 1)) (j : B.SmoothEmbedding M),
      range j.map = {x | ρ x = 0} := by
  have hsurj (x : M.Point) (hx : ρ x = 0) :
      Function.Surjective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ x) := by
    apply LinearMap.surjective (f :=
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ x : Model d →L[ℝ] ℝ).toLinearMap)
    intro he
    exact hregular x hx (ContinuousLinearMap.coe_injective he)
  have h := exists_regularLevel_embedding M ρ 0 hρ hsurj
  rw [Module.finrank_self] at h
  exact h

private def scalarSublevelDefiningFunction {d : ℕ} (M : SmoothManifold d)
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    (hregular : ∀ x, ρ x = 0 → mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ x ≠ 0)
    (x : M.Point) (hx : x ∈ frontier {y | ρ y ≤ 0}) :
    BoundaryDefiningFunction M {y | ρ y ≤ 0} x where
  neighbourhood := univ
  open_neighbourhood := isOpen_univ
  mem_neighbourhood := mem_univ _
  rho := ρ
  smooth_rho := hρ.contMDiffOn
  sublevel := fun _ _ => Iff.rfl
  zero_level := by
    intro y _
    rw [M.frontier_scalar_sublevel_of_regular_zero ρ hρ hregular]
    rfl
  regular := hregular x (by
    rwa [M.frontier_scalar_sublevel_of_regular_zero ρ hρ hregular] at hx)

set_option backward.isDefEq.respectTransparency false in
/-- A native compact domain on the literal scalar sublevel. The boundary
manifold and its smooth embedding are constructed from regularity, and the
boundary is empty in dimension zero. -/
def regularSublevelCompactDomain {d : ℕ} (M : SmoothManifold d)
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    (hcompact : IsCompact {x : M.Point | ρ x ≤ 0})
    (hregular : ∀ x, ρ x = 0 → mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ x ≠ 0) :
    CompactDomain d := by
  let H := exists_scalarRegularLevel_embedding M ρ hρ hregular
  let B := H.choose
  let j := H.choose_spec.choose
  have hj : range j.map = {x | ρ x = 0} := H.choose_spec.choose_spec
  exact
    { extension := M
      carrier := {x | ρ x ≤ 0}
      compact := hcompact
      defining := scalarSublevelDefiningFunction M ρ hρ hregular
      boundary := B
      boundaryInclusion := j
      boundary_range := hj.trans
        (M.frontier_scalar_sublevel_of_regular_zero ρ hρ hregular).symm
      zero_boundary := by
        intro hd
        refine ⟨fun b => ?_⟩
        have hb : ρ (j.map b) = 0 := by
          have h : j.map b ∈ range j.map := ⟨b, rfl⟩
          rwa [hj] at h
        apply hregular (j.map b) hb
        subst d
        ext v
        change Model 0 at v
        have hv : v = (0 : Model 0) := Subsingleton.elim _ _
        simp [hv] }

/-- The native compact domain's frontier is precisely the regular zero level. -/
theorem regularSublevelCompactDomain_frontier {d : ℕ} (M : SmoothManifold d)
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    (hcompact : IsCompact {x : M.Point | ρ x ≤ 0})
    (hregular : ∀ x, ρ x = 0 → mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ x ≠ 0) :
    frontier (regularSublevelCompactDomain M ρ hρ hcompact hregular).carrier =
      {x : M.Point | ρ x = 0} :=
  M.frontier_scalar_sublevel_of_regular_zero ρ hρ hregular

/-- Strict outwardness of an actual field forces regularity of the scalar
zero level, since the zero differential would evaluate to zero on that field. -/
theorem regular_zero_of_scalarDerivative_pos {d : ℕ} (M : SmoothManifold d)
    (ρ : M.Point → ℝ) (Z : (x : M.Point) → M.Tangent x)
    (hout : ∀ x, ρ x = 0 → 0 < M.scalarDerivative ρ x (Z x)) :
    ∀ x, ρ x = 0 → mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ x ≠ 0 := by
  intro x hx he
  have hp := hout x hx
  unfold scalarDerivative at hp
  rw [he, zero_apply] at hp
  exact (lt_irrefl 0) hp

set_option backward.isDefEq.respectTransparency false in
/-- A smooth globally symplectic primitive with strictly outward actual
Liouville field makes the compact scalar sublevel into a native Liouville
domain. Outwardness itself supplies the regularity needed to construct the
boundary; completeness of the ambient field is not required. -/
def regularSublevelLiouvilleDomain {d : ℕ} (M : SmoothManifold d)
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    (hcompact : IsCompact {x : M.Point | ρ x ≤ 0})
    (alpha : M.Form 1) (halpha : M.IsSmoothForm alpha)
    (hω : M.IsSymplecticOn (M.exteriorDerivative alpha) univ)
    (hout : ∀ x, ρ x = 0 →
      0 < M.scalarDerivative ρ x (M.liouvilleVector alpha x)) : LiouvilleDomain d := by
  let hr := regular_zero_of_scalarDerivative_pos M ρ (M.liouvilleVector alpha) hout
  let D := regularSublevelCompactDomain M ρ hρ hcompact hr
  exact
    { domain := D
      liouville :=
        { primitive := alpha
          smooth_primitive := halpha
          symplectic := ⟨hω.1, fun x _ => hω.2.1 x (mem_univ _),
            fun x _ => hω.2.2 x (mem_univ _)⟩
          field := M.liouvilleVector alpha
          smooth_field := M.isSmoothVectorField_liouvilleVector alpha halpha
            (fun x => hω.2.2 x (mem_univ _))
          contraction := fun x _ => M.liouvilleVector_contraction alpha x
            (M.liouvilleEquation_exists alpha x (hω.2.2 x (mem_univ _)))
          outward := by
            intro x hx
            change 0 < M.scalarDerivative ρ x (M.liouvilleVector alpha x)
            apply hout x
            rwa [regularSublevelCompactDomain_frontier M ρ hρ hcompact hr] at hx } }

/-- The constructed Liouville domain retains the literal zero frontier,
with no separately chosen carrier or boundary representation. -/
theorem regularSublevelLiouvilleDomain_frontier {d : ℕ} (M : SmoothManifold d)
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    (hcompact : IsCompact {x : M.Point | ρ x ≤ 0})
    (alpha : M.Form 1) (halpha : M.IsSmoothForm alpha)
    (hω : M.IsSymplecticOn (M.exteriorDerivative alpha) univ)
    (hout : ∀ x, ρ x = 0 →
      0 < M.scalarDerivative ρ x (M.liouvilleVector alpha x)) :
    frontier (regularSublevelLiouvilleDomain M ρ hρ hcompact alpha halpha hω hout).domain.carrier =
      {x : M.Point | ρ x = 0} :=
  M.frontier_scalar_sublevel_of_regular_zero ρ hρ
    (regular_zero_of_scalarDerivative_pos M ρ (M.liouvilleVector alpha) hout)

end FsFltz.Geometry
