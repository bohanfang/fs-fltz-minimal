import FsFltz.Geometry.Liouville
import FsFltz.Geometry.ExteriorDerivative
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Pointwise boundary foundations for a Liouville domain

The defining-function convention in `geoemtric-part-fsf.tex`, lines 119–130,
and `def:pair`, lines 132–160, determines the boundary tangent hyperplane.
This file proves tangency, the transverse Liouville decomposition, and the
nowhere-zero boundary primitive from the existing domain and Liouville data.
These are producers for the contact-form foundation in `sec:lean`, lines
783–814. `ContactVolume` uses these results to prove boundary contact in
every positive even ambient dimension.
-/

noncomputable section
open scoped Manifold ContDiff BigOperators
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace CompactDomain

/-- The boundary presentation parametrizes points of the actual frontier. -/
theorem boundaryInclusion_mem_frontier {d : ℕ} (D : CompactDomain d)
    (x : D.boundary.Point) : D.boundaryInclusion.map x ∈ frontier D.carrier := by
  rw [← D.boundary_range]
  exact ⟨x, rfl⟩

/-- Compactness places the presented boundary in the domain itself. -/
theorem boundaryInclusion_mem_carrier {d : ℕ} (D : CompactDomain d)
    (x : D.boundary.Point) : D.boundaryInclusion.map x ∈ D.carrier :=
  D.compact.isClosed.frontier_subset (D.boundaryInclusion_mem_frontier x)

/-- The actual boundary differential is annihilated by every local defining
function at its base point. Tangency is derived from the zero-level identity. -/
theorem boundaryInclusion_derivative_tangent {d : ℕ} (D : CompactDomain d)
    (x : D.boundary.Point)
    (ρ : BoundaryDefiningFunction D.extension D.carrier (D.boundaryInclusion.map x))
    (v : D.boundary.Tangent x) :
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ.rho (D.boundaryInclusion.map x)
      (mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d) D.boundaryInclusion.map x v) = 0 := by
  have hρ := (ρ.smooth_rho.contMDiffAt
    (ρ.open_neighbourhood.mem_nhds ρ.mem_neighbourhood)).mdifferentiableAt (by simp)
  have hj := D.boundaryInclusion.map.contMDiff.mdifferentiable (by simp) x
  have hz : ρ.rho ∘ D.boundaryInclusion.map =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [D.boundaryInclusion.map.contMDiff.continuous.continuousAt.preimage_mem_nhds
      (ρ.open_neighbourhood.mem_nhds ρ.mem_neighbourhood)] with y hy
    exact (ρ.zero_level _ hy).mp (D.boundaryInclusion_mem_frontier y)
  have hzero : mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, ℝ)
      (ρ.rho ∘ D.boundaryInclusion.map) x = 0 := by
    simpa using hz.mfderiv_eq (I := 𝓘(ℝ, Model (d - 1))) (I' := 𝓘(ℝ, ℝ))
  rw [← mfderiv_comp_apply x hρ hj v, hzero]
  rfl

end CompactDomain

/-- An immersed codimension-one tangent space and a transverse vector span
the entire ambient tangent space. -/
theorem tangent_prod_span_bijective {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) (p : F →ₗ[ℝ] ℝ) (Z : F)
    (hA : Function.Injective A) (hpA : ∀ v, p (A v) = 0) (hpZ : p Z ≠ 0)
    (hdim : Module.finrank ℝ E + 1 = Module.finrank ℝ F) :
    Function.Bijective (A.coprod ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight Z)) := by
  have hinj : Function.Injective
      (A.coprod ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight Z)) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro q hq
    have hpq := congrArg p hq
    have hs : q.2 = 0 := by
      have he : q.2 * p Z = 0 := by simpa only
        [LinearMap.coprod_apply, LinearMap.smulRight_apply, LinearMap.id_apply,
        map_add, hpA, map_smul, zero_add, map_zero, smul_eq_mul] using hpq
      exact (mul_eq_zero.mp he).resolve_right hpZ
    have hv : A q.1 = 0 := by
      simpa only [LinearMap.coprod_apply, LinearMap.smulRight_apply, LinearMap.id_apply,
        hs, zero_smul, add_zero] using hq
    exact Prod.ext (hA (hv.trans (map_zero A).symm)) hs
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  simpa only [Module.finrank_prod, Module.finrank_self] using hdim

namespace CompactDomain

/-- The tangent image of the smooth boundary presentation is exactly the
kernel of a local defining function's differential. -/
theorem boundaryInclusion_range_eq_ker {d : ℕ} (D : CompactDomain d)
    (x : D.boundary.Point)
    (ρ : BoundaryDefiningFunction D.extension D.carrier (D.boundaryInclusion.map x)) :
    LinearMap.range (mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d)
      D.boundaryInclusion.map x).toLinearMap =
    LinearMap.ker (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ.rho
      (D.boundaryInclusion.map x)).toLinearMap := by
  classical
  let A := (mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d)
    D.boundaryInclusion.map x).toLinearMap
  let p : D.extension.Tangent (D.boundaryInclusion.map x) →ₗ[ℝ] ℝ :=
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ.rho
    (D.boundaryInclusion.map x)).toLinearMap
  have hd : d ≠ 0 := by
    intro hd
    subst d
    have : IsEmpty D.boundary.Point := D.zero_boundary rfl
    exact isEmptyElim x
  obtain ⟨Z, hZ⟩ : ∃ Z, p Z ≠ 0 := by
    by_contra h
    push Not at h
    apply ρ.regular
    ext Z
    exact h Z
  have hpA (v) : p (A v) = 0 := D.boundaryInclusion_derivative_tangent x ρ v
  have hdim : Module.finrank ℝ (D.boundary.Tangent x) + 1 =
      Module.finrank ℝ (D.extension.Tangent (D.boundaryInclusion.map x)) := by
    change Module.finrank ℝ (Model (d - 1)) + 1 = Module.finrank ℝ (Model d)
    rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
    omega
  have hbij := tangent_prod_span_bijective A p Z (D.boundaryInclusion.immersion x)
    hpA hZ hdim
  apply le_antisymm
  · rintro w ⟨v, rfl⟩
    exact hpA v
  · intro w hw
    obtain ⟨⟨v, s⟩, he⟩ := hbij.2 w
    have hsw : s * p Z = 0 := by
      have hpe := congrArg p he
      simpa only [LinearMap.coprod_apply, LinearMap.smulRight_apply, LinearMap.id_apply,
        map_add, hpA, map_smul, zero_add, smul_eq_mul, show p w = 0 from hw] using hpe
    have hs := (mul_eq_zero.mp hsw).resolve_right hZ
    exact ⟨v, by simpa only [LinearMap.coprod_apply, LinearMap.smulRight_apply,
      LinearMap.id_apply, hs, zero_smul, add_zero] using he⟩

end CompactDomain

namespace LiouvilleStructure

set_option backward.isDefEq.respectTransparency false in
/-- Every ambient tangent vector at a boundary point decomposes into an
actual boundary tangent vector and a multiple of the outward Liouville field. -/
theorem boundary_tangent_decomposition {d : ℕ} {D : CompactDomain d}
    (L : LiouvilleStructure D) (x : D.boundary.Point)
    (w : D.extension.Tangent (D.boundaryInclusion.map x)) :
    ∃ (v : D.boundary.Tangent x) (s : ℝ),
      mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d) D.boundaryInclusion.map x v +
        s • L.field (D.boundaryInclusion.map x) = w := by
  let ρ := D.defining _ (D.boundaryInclusion_mem_frontier x)
  let p : D.extension.Tangent (D.boundaryInclusion.map x) →ₗ[ℝ] ℝ :=
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ρ.rho
    (D.boundaryInclusion.map x)).toLinearMap
  have hpZ : p (L.field (D.boundaryInclusion.map x)) ≠ 0 :=
    ne_of_gt (L.outward _ (D.boundaryInclusion_mem_frontier x))
  let s := p w / p (L.field (D.boundaryInclusion.map x))
  have hker : w - s • L.field (D.boundaryInclusion.map x) ∈ LinearMap.ker p := by
    change p (w - s • L.field (D.boundaryInclusion.map x)) = 0
    simp only [map_sub, map_smul, smul_eq_mul, s, div_mul_cancel₀ _ hpZ, sub_self]
  have heq : LinearMap.range (mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d)
      D.boundaryInclusion.map x).toLinearMap = LinearMap.ker p :=
    D.boundaryInclusion_range_eq_ker x ρ
  rw [← heq] at hker
  obtain ⟨v, hv⟩ := hker
  change mfderiv 𝓘(ℝ, Model (d - 1)) 𝓘(ℝ, Model d) D.boundaryInclusion.map x v =
    w - s • L.field (D.boundaryInclusion.map x) at hv
  exact ⟨v, s, by rw [hv]; exact sub_add_cancel _ _⟩

/-- Alternation and the contraction equation force the primitive to vanish
on its own Liouville field. -/
theorem evalOne_field_eq_zero {d : ℕ} {D : CompactDomain d}
    (L : LiouvilleStructure D) (x : D.extension.Point) (hx : x ∈ D.carrier) :
    evalOne L.primitive x (L.field x) = 0 := by
  rw [← L.contraction x hx (L.field x)]
  exact (D.extension.exteriorDerivative L.primitive x).map_eq_zero_of_eq
    ![L.field x, L.field x] (i := 0) (j := 1) rfl (by decide)

end LiouvilleStructure

namespace SmoothManifold

private theorem contDiffAt_oneForm_compContinuousLinearMap {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (a : G → F [⋀^Fin 1]→L[ℝ] ℝ) (B : G → E →L[ℝ] F) (z : G)
    (ha : ContDiffAt ℝ ∞ a z) (hB : ContDiffAt ℝ ∞ B z) :
    ContDiffAt ℝ ∞ (fun y => (a y).compContinuousLinearMap (B y)) z := by
  let eF := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := F) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  let eE := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  have h := (eF.symm.contDiff.contDiffAt.comp z ha).clm_comp hB
  have hs := eE.contDiff.contDiffAt.comp z h
  convert hs using 1
  ext y vs
  change a y (fun i => B y (vs i)) = a y (fun _ => B y (vs 0))
  congr 1
  funext i
  rw [Fin.eq_zero i]

/-- Pullback preserves smooth one-forms. The chart proof uses the smooth
coordinate map and its actual derivative, with no smoothness certificate for
the resulting form supplied as an input. -/
theorem isSmoothForm_pullback_one {d e : ℕ} (M : SmoothManifold d)
    (N : SmoothManifold e) (f : M.SmoothMap N) (α : N.Form 1)
    (hα : N.IsSmoothForm α) : M.IsSmoothForm (M.pullback N f α) := by
  intro a y hy
  let c := chartAt (Model d) a
  let x := c.symm y
  let b := chartAt (Model e) (f x)
  let g := b ∘ f ∘ c.symm
  have hx : f x ∈ b.source := mem_chart_source _ _
  have hA : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ c.symm y :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (x := a)).contMDiffAt
      (c.open_target.mem_nhds hy)
  have hB : ContMDiffAt 𝓘(ℝ, Model e) 𝓘(ℝ, Model e) ∞ b (f x) :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model e)) (x := f x)).contMDiffAt
      (b.open_source.mem_nhds hx)
  have hg : ContDiffAt ℝ ∞ g y :=
    (hB.comp y (f.contMDiff.contMDiffAt.comp y hA)).contDiffAt
  have hcoeff : ContDiffAt ℝ ∞ (N.formInChart (f x) α) (g y) :=
    (hα (f x)).contDiffAt (b.open_target.mem_nhds (b.map_source hx))
  have hs := contDiffAt_oneForm_compContinuousLinearMap
    (fun z => N.formInChart (f x) α (g z)) (fderiv ℝ g) y
    (hcoeff.comp y hg) (hg.fderiv_right (by simp))
  have hnb : ∀ᶠ z in 𝓝 y, f (c.symm z) ∈ b.source :=
    (f.contMDiff.continuous.continuousAt.comp (c.continuousAt_symm hy)).preimage_mem_nhds
      (b.open_source.mem_nhds hx)
  have hlocal : M.formInChart a (M.pullback N f α) =ᶠ[𝓝 y]
      fun z => (N.formInChart (f x) α (g z)).compContinuousLinearMap (fderiv ℝ g z) := by
    filter_upwards [c.open_target.mem_nhds hy, hnb] with z hz hzb
    exact M.formInChart_pullback N α a (f x) z hz hzb
      (f.contMDiff.mdifferentiableAt (by simp))
  exact (hs.congr_of_eventuallyEq hlocal).contDiffWithinAt

theorem evalOne_add {d : ℕ} {M : SmoothManifold d} (α : M.Form 1)
    (x : M.Point) (v w : M.Tangent x) :
    evalOne α x (v + w) = evalOne α x v + evalOne α x w := by
  have hc (u : M.Tangent x) : ![u] = fun _ : Fin 1 => u := by
    ext i
    fin_cases i
    rfl
  simpa only [hc, ContinuousAlternatingMap.coe_toAlternatingMap, evalOne] using
    (α x).toAlternatingMap.map_vecCons_add ![] v w

theorem evalOne_smul {d : ℕ} {M : SmoothManifold d} (α : M.Form 1)
    (x : M.Point) (s : ℝ) (v : M.Tangent x) :
    evalOne α x (s • v) = s * evalOne α x v := by
  have hc (u : M.Tangent x) : ![u] = fun _ : Fin 1 => u := by
    ext i
    fin_cases i
    rfl
  simpa only [hc, ContinuousAlternatingMap.coe_toAlternatingMap, evalOne, smul_eq_mul] using
    (α x).toAlternatingMap.map_vecCons_smul ![] s v

@[simp] theorem contactVolume_zero {d : ℕ} (M : SmoothManifold d) (α : M.Form 1)
    (x : M.Point) (v : Fin 1 → M.Tangent x) :
    M.contactVolume α 0 x v = evalOne α x (v 0) := by
  simp [contactVolume]

end SmoothManifold

namespace LiouvilleStructure

/-- The restriction of a Liouville primitive to the actual boundary tangent
space is nowhere zero. Symplectic nondegeneracy and outwardness are both used. -/
theorem boundaryForm_exists_eval_ne_zero {d : ℕ} {D : CompactDomain d}
    (L : LiouvilleStructure D) (x : D.boundary.Point) :
    ∃ v : D.boundary.Tangent x, evalOne (D.boundaryForm L.primitive) x v ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hx := D.boundaryInclusion_mem_carrier x
  have hzero (w : D.extension.Tangent (D.boundaryInclusion.map x)) :
      evalOne L.primitive (D.boundaryInclusion.map x) w = 0 := by
    obtain ⟨v, s, rfl⟩ := L.boundary_tangent_decomposition x w
    rw [evalOne_add, evalOne_smul, L.evalOne_field_eq_zero _ hx, mul_zero, add_zero]
    exact h v
  have hfield : L.field (D.boundaryInclusion.map x) = 0 :=
    L.symplectic.2.2 _ hx _ (fun w => (L.contraction _ hx w).trans (hzero w))
  have hout := L.outward _ (D.boundaryInclusion_mem_frontier x)
  rw [hfield] at hout
  simp only [scalarDerivative, map_zero] at hout
  exact (lt_irrefl (0 : ℝ)) hout

/-- In a two-dimensional Liouville domain, the defining contact volume on
the one-dimensional boundary is nonzero at every point. -/
theorem boundary_contactVolume_dimTwo {D : CompactDomain 2} (L : LiouvilleStructure D)
    (x : D.boundary.Point) :
    ∃ v : Fin 1 → D.boundary.Tangent x,
      D.boundary.contactVolume (D.boundaryForm L.primitive) 0 x v ≠ 0 := by
  obtain ⟨v, hv⟩ := L.boundaryForm_exists_eval_ne_zero x
  exact ⟨fun _ => v, by simpa using hv⟩

/-- The restricted primitive is a contact form on a two-dimensional Liouville
domain's one-dimensional boundary, including the source's `n = 1` case. -/
theorem boundaryForm_isContactForm_dimTwo {D : CompactDomain 2} (L : LiouvilleStructure D) :
    D.boundary.IsContactForm (D.boundaryForm L.primitive) 0 := by
  refine ⟨rfl, ?_, L.boundary_contactVolume_dimTwo⟩
  exact D.boundary.isSmoothForm_pullback_one D.extension D.boundaryInclusion.map
    L.primitive L.smooth_primitive

end LiouvilleStructure

end FsFltz.Geometry
