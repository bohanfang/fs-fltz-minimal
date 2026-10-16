import FsFltz.Geometry.BoundaryNondegeneracy
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The actual boundary contact hyperplane

Source: `geoemtric-part-fsf.tex`, differential-geometric conventions, lines
119–130; `def:pair`, lines 132–160; and `sec:lean`, lines 783–814.

Put `α = j*λ`, `β = dα`, and `ω = dλ`. Naturality gives `β = j*ω`.
If `v ∈ ker α` annihilates `ker α` under `β`, choose `u` with `α(u) ≠ 0`.
For every boundary tangent `w`, subtract `(α(w)/α(u))u` to obtain an element
of `ker α`. Hence `ω(jv,jw) = c α(w)`, where `c = β(v,u)/α(u)`.
Contraction and alternation show that `jv - cZ` annihilates both the boundary
tangents and `Z`. The transverse decomposition then shows it annihilates all
ambient tangents, so symplectic nondegeneracy gives `jv = cZ`. Applying the
defining-function differential and outwardness gives `c = 0`; immersion
finally gives `v = 0`.

This proves nondegeneracy of the actual differential on the actual primitive
kernel in every dimension. `SymplecticBasis` and `ContactVolume` convert this
result to nonvanishing of the existing permutation-sum top contact volume.
-/

noncomputable section
open scoped Manifold ContDiff BigOperators

namespace FsFltz.Geometry
open SmoothManifold

namespace SmoothManifold

theorem evalOne_sub {d : ℕ} {M : SmoothManifold d} (α : M.Form 1)
    (x : M.Point) (v w : M.Tangent x) :
    evalOne α x (v - w) = evalOne α x v - evalOne α x w := by
  have hc (u : M.Tangent x) : ![u] = fun _ : Fin 1 => u := by
    ext i
    rw [Fin.eq_zero i]
    rfl
  simpa only [hc, evalOne] using (α x).map_vecCons_sub v w ![]

theorem evalTwo_add_left {d : ℕ} {M : SmoothManifold d} (β : M.Form 2)
    (x : M.Point) (v w z : M.Tangent x) :
    evalTwo β x (v + w) z = evalTwo β x v z + evalTwo β x w z :=
  (β x).toAlternatingMap.map_vecCons_add ![z] v w

theorem evalTwo_smul_left {d : ℕ} {M : SmoothManifold d} (β : M.Form 2)
    (x : M.Point) (s : ℝ) (v w : M.Tangent x) :
    evalTwo β x (s • v) w = s * evalTwo β x v w :=
  (β x).toAlternatingMap.map_vecCons_smul ![w] s v

theorem evalTwo_sub_left {d : ℕ} {M : SmoothManifold d} (β : M.Form 2)
    (x : M.Point) (v w z : M.Tangent x) :
    evalTwo β x (v - w) z = evalTwo β x v z - evalTwo β x w z :=
  (β x).map_vecCons_sub v w ![z]

theorem evalTwo_swap {d : ℕ} {M : SmoothManifold d} (β : M.Form 2)
    (x : M.Point) (v w : M.Tangent x) :
    evalTwo β x v w = -evalTwo β x w v := by
  have hs : (![w, v] : Fin 2 → M.Tangent x) ∘ Equiv.swap 0 1 = ![v, w] := by
    ext i
    fin_cases i <;> simp
  simpa only [hs, ContinuousAlternatingMap.coe_toAlternatingMap, evalTwo] using
    (β x).toAlternatingMap.map_swap ![w, v] (i := 0) (j := 1) (by decide)

theorem evalTwo_sub_right {d : ℕ} {M : SmoothManifold d} (β : M.Form 2)
    (x : M.Point) (v w z : M.Tangent x) :
    evalTwo β x v (w - z) = evalTwo β x v w - evalTwo β x v z := by
  rw [evalTwo_swap β x v (w - z), evalTwo_sub_left]
  rw [evalTwo_swap β x w v, evalTwo_swap β x z v]
  ring

theorem evalTwo_smul_right {d : ℕ} {M : SmoothManifold d} (β : M.Form 2)
    (x : M.Point) (s : ℝ) (v w : M.Tangent x) :
    evalTwo β x v (s • w) = s * evalTwo β x v w := by
  rw [evalTwo_swap β x v (s • w), evalTwo_smul_left, evalTwo_swap β x w v]
  ring

/-- The intrinsic kernel of a one-form, as a native tangent submodule. -/
def contactHyperplane {d : ℕ} (M : SmoothManifold d) (α : M.Form 1) (x : M.Point) :
    Submodule ℝ (M.Tangent x) :=
  LinearMap.ker ((ContinuousAlternatingMap.ofSubsingleton
    ℝ (M.Tangent x) ℝ (0 : Fin 1)).symm (α x)).toLinearMap

@[simp] theorem mem_contactHyperplane {d : ℕ} (M : SmoothManifold d)
    (α : M.Form 1) (x : M.Point) (v : M.Tangent x) :
    v ∈ M.contactHyperplane α x ↔ evalOne α x v = 0 := Iff.rfl

set_option backward.isDefEq.respectTransparency false in
/-- A nonzero one-form has a kernel of codimension one. -/
theorem finrank_contactHyperplane_add_one {d : ℕ} (M : SmoothManifold d)
    (α : M.Form 1) (x : M.Point) (hα : ∃ v, evalOne α x v ≠ 0) :
    Module.finrank ℝ (M.contactHyperplane α x) + 1 = d := by
  let f : M.Tangent x →ₗ[ℝ] ℝ := ((ContinuousAlternatingMap.ofSubsingleton
    ℝ (M.Tangent x) ℝ (0 : Fin 1)).symm (α x)).toLinearMap
  have hf : f ≠ 0 := by
    intro hf
    obtain ⟨v, hv⟩ := hα
    apply hv
    change f v = 0
    rw [hf]
    rfl
  have he := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hdim : Module.finrank ℝ (M.Tangent x) = d := by
    change Module.finrank ℝ (Model d) = d
    exact finrank_euclideanSpace_fin
  simpa only [contactHyperplane, f, hdim] using he

/-- Restriction of the actual exterior derivative to the primitive kernel. -/
def contactHyperplaneDifferential {d : ℕ} (M : SmoothManifold d) (α : M.Form 1)
    (x : M.Point) :
    M.contactHyperplane α x [⋀^Fin 2]→L[ℝ] ℝ :=
  (M.exteriorDerivative α x).compContinuousLinearMap (M.contactHyperplane α x).subtypeL

@[simp] theorem contactHyperplaneDifferential_apply {d : ℕ} (M : SmoothManifold d)
    (α : M.Form 1) (x : M.Point) (v w : M.contactHyperplane α x) :
    M.contactHyperplaneDifferential α x ![v, w] =
      evalTwo (M.exteriorDerivative α) x v w := by
  change (M.exteriorDerivative α x) (fun i => (↑(![v, w] i) : M.Tangent x)) =
    (M.exteriorDerivative α x) ![(v : M.Tangent x), (w : M.Tangent x)]
  congr 1
  ext i
  fin_cases i <;> rfl

end SmoothManifold

namespace LiouvilleStructure

/-- Naturality identifies the actual boundary differential with the restriction
of the ambient symplectic differential. -/
theorem boundaryForm_exteriorDerivative {d : ℕ} {D : CompactDomain d}
    (L : LiouvilleStructure D) :
    D.boundary.exteriorDerivative (D.boundaryForm L.primitive) =
      D.boundary.pullback D.extension D.boundaryInclusion.map
        (D.extension.exteriorDerivative L.primitive) :=
  D.boundary.exteriorDerivative_pullback D.extension D.boundaryInclusion.map
    L.primitive L.smooth_primitive

set_option backward.isDefEq.respectTransparency false in
/-- The actual boundary differential is nondegenerate on the kernel of the
restricted primitive. No contact-volume certificate is assumed. -/
theorem boundaryForm_differential_nondegenerate_on_kernel {d : ℕ} {D : CompactDomain d}
    (L : LiouvilleStructure D) (x : D.boundary.Point) (v : D.boundary.Tangent x)
    (hv : evalOne (D.boundaryForm L.primitive) x v = 0)
    (hβ : ∀ w : D.boundary.Tangent x,
      evalOne (D.boundaryForm L.primitive) x w = 0 →
      evalTwo (D.boundary.exteriorDerivative (D.boundaryForm L.primitive)) x v w = 0) :
    v = 0 := by
  let y := D.boundaryInclusion.map x
  let A := mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d) D.boundaryInclusion.map x
  let α := D.boundaryForm L.primitive
  let β := D.boundary.exteriorDerivative α
  let η := D.extension.exteriorDerivative L.primitive
  have hx := D.boundaryInclusion_mem_carrier x
  have hα (w : D.boundary.Tangent x) : evalOne α x w = evalOne L.primitive y (A w) := rfl
  have hres (w z : D.boundary.Tangent x) : evalTwo β x w z = evalTwo η y (A w) (A z) := by
    dsimp [β, α]
    rw [L.boundaryForm_exteriorDerivative]
    change (η y) (fun i => A (![w, z] i)) = (η y) ![A w, A z]
    congr 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨u, hu⟩ := L.boundaryForm_exists_eval_ne_zero x
  change evalOne α x u ≠ 0 at hu
  let c := evalTwo β x v u / evalOne α x u
  have hboundary (w : D.boundary.Tangent x) :
      evalTwo η y (A v) (A w) = c * evalOne α x w := by
    let s := evalOne α x w / evalOne α x u
    have hkernel : evalOne α x (w - s • u) = 0 := by
      rw [evalOne_sub, evalOne_smul]
      simp only [s, div_mul_cancel₀ _ hu, sub_self]
    have he := hβ (w - s • u) hkernel
    change evalTwo β x v (w - s • u) = 0 at he
    rw [evalTwo_sub_right, evalTwo_smul_right] at he
    rw [← hres]
    calc
      evalTwo β x v w = s * evalTwo β x v u := sub_eq_zero.mp he
      _ = c * evalOne α x w := by dsimp [s, c]; ring
  have hZ : evalTwo η y (A v) (L.field y) = 0 := by
    rw [evalTwo_swap, L.contraction y hx, ← hα, hv, neg_zero]
  have hZZ : evalTwo η y (L.field y) (L.field y) = 0 := by
    rw [L.contraction y hx, L.evalOne_field_eq_zero y hx]
  have hzero : A v - c • L.field y = 0 := by
    apply L.symplectic.2.2 y hx
    intro w
    obtain ⟨z, s, hz⟩ := L.boundary_tangent_decomposition x w
    rw [← hz]
    change evalTwo η y (A v - c • L.field y) (A z + s • L.field y) = 0
    rw [evalTwo_swap, evalTwo_add_left, evalTwo_smul_left]
    rw [evalTwo_swap η y (A z) _, evalTwo_swap η y (L.field y) _]
    rw [evalTwo_sub_left, evalTwo_sub_left, evalTwo_smul_left, evalTwo_smul_left]
    rw [hboundary, L.contraction y hx, ← hα, hZ, hZZ]
    ring
  have heq : A v = c • L.field y := sub_eq_zero.mp hzero
  let ρ := D.defining y (D.boundaryInclusion_mem_frontier x)
  let p : D.extension.Tangent y →L[ℝ] ℝ :=
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ.rho y
  have hpZ : p (L.field y) ≠ 0 :=
    ne_of_gt (L.outward y (D.boundaryInclusion_mem_frontier x))
  have hpA : p (A v) = 0 := D.boundaryInclusion_derivative_tangent x ρ v
  have hc : c = 0 := by
    have h := congrArg p heq
    rw [hpA, map_smul] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hpZ
  have hAv : A v = A 0 := by rw [heq, hc, zero_smul, map_zero]
  exact D.boundaryInclusion.immersion x hAv

/-- The canonical continuous alternating restriction to the contact hyperplane
is pointwise nondegenerate, in every ambient dimension. -/
theorem boundary_contactHyperplaneDifferential_nondegenerate {d : ℕ} {D : CompactDomain d}
    (L : LiouvilleStructure D) (x : D.boundary.Point)
    (v : D.boundary.contactHyperplane (D.boundaryForm L.primitive) x)
    (hv : ∀ w : D.boundary.contactHyperplane (D.boundaryForm L.primitive) x,
      D.boundary.contactHyperplaneDifferential (D.boundaryForm L.primitive) x ![v, w] = 0) :
    v = 0 := by
  apply Subtype.ext
  apply L.boundaryForm_differential_nondegenerate_on_kernel x
  · exact (D.boundary.mem_contactHyperplane _ _ _).mp v.property
  · intro w hw
    simpa using hv ⟨w, (D.boundary.mem_contactHyperplane _ _ _).mpr hw⟩

/-- The boundary primitive kernel has the expected dimension `d - 2`,
including the zero-dimensional kernel of a two-dimensional domain. -/
theorem boundary_contactHyperplane_finrank {d : ℕ} {D : CompactDomain d}
    (L : LiouvilleStructure D) (x : D.boundary.Point) :
    Module.finrank ℝ (D.boundary.contactHyperplane (D.boundaryForm L.primitive) x) = d - 2 := by
  have h := D.boundary.finrank_contactHyperplane_add_one (D.boundaryForm L.primitive) x
    (L.boundaryForm_exists_eval_ne_zero x)
  omega

end LiouvilleStructure
end FsFltz.Geometry
