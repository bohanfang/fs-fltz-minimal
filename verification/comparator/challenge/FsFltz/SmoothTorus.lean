import FsFltz.Differential
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# Smooth structure on the quotient torus

The quotient circles of `sec:data` (lines 57–85 of `geoemtric-part-fsf.tex`)
carry the smooth atlas transported from the unit circle through the literal
period-`2π` homeomorphism. This addresses the quotient-manifold foundation in
`sec:lean`, lines 778–782; no geometric existence conclusion is asserted.
-/

noncomputable section

open scoped Manifold ContDiff
open Topology

namespace FsFltz

abbrev AngleModel := EuclideanSpace ℝ (Fin 1)

/-- The period-`2π` quotient identified with the unit circle. -/
def angleCircleHomeomorph : AddCircle (2 * Real.pi) ≃ₜ Circle :=
  AddCircle.homeomorphCircle'

/-- Explicit pullback atlas, retaining the quotient topology. -/
instance angleChartedSpace : ChartedSpace AngleModel (AddCircle (2 * Real.pi)) where
  atlas := {angleCircleHomeomorph.transOpenPartialHomeomorph e |
    e ∈ atlas AngleModel Circle}
  chartAt x := angleCircleHomeomorph.transOpenPartialHomeomorph
    (chartAt AngleModel (angleCircleHomeomorph x))
  mem_chart_source x := mem_chart_source AngleModel (angleCircleHomeomorph x)
  chart_mem_atlas _x := ⟨_, chart_mem_atlas _ _, rfl⟩

instance angleIsManifold : IsManifold (𝓡 1) ∞ (AddCircle (2 * Real.pi)) where
  compatible := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    simp only [Homeomorph.transOpenPartialHomeomorph_eq_trans,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc]
    rw [← Homeomorph.symm_toOpenPartialHomeomorph,
      ← OpenPartialHomeomorph.trans_assoc angleCircleHomeomorph.symm.toOpenPartialHomeomorph,
      ← Homeomorph.trans_toOpenPartialHomeomorph, Homeomorph.symm_trans_self,
      Homeomorph.refl_toOpenPartialHomeomorph, OpenPartialHomeomorph.refl_trans]
    exact StructureGroupoid.compatible (contDiffGroupoid ∞ (𝓡 1)) he he'

/-- The explicit quotient-circle identification is smooth in its transported atlas. -/
theorem contMDiff_angleCircleHomeomorph :
    ContMDiff (𝓡 1) (𝓡 1) ∞ angleCircleHomeomorph := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨angleCircleHomeomorph.continuous.continuousAt, ?_⟩
  let e := chartAt AngleModel (angleCircleHomeomorph x)
  have he : e (angleCircleHomeomorph x) ∈ e.target := e.map_source (mem_chart_source _ _)
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_id.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds he] with y hy
  change e (angleCircleHomeomorph (angleCircleHomeomorph.symm (e.symm y))) = y
  simpa only [Homeomorph.apply_symm_apply] using e.right_inv hy

/-- The inverse identification is smooth as well. -/
theorem contMDiff_angleCircleHomeomorph_symm :
    ContMDiff (𝓡 1) (𝓡 1) ∞ angleCircleHomeomorph.symm := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨angleCircleHomeomorph.symm.continuous.continuousAt, ?_⟩
  let e := chartAt AngleModel x
  have he : e x ∈ e.target := e.map_source (mem_chart_source _ _)
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_id.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds he] with y hy
  change (chartAt AngleModel (angleCircleHomeomorph (angleCircleHomeomorph.symm x)))
    (angleCircleHomeomorph (angleCircleHomeomorph.symm (e.symm y))) = y
  simpa only [Homeomorph.apply_symm_apply] using e.right_inv hy

/-- The standard projection from a real angle is smooth in this quotient atlas. -/
theorem contMDiff_angle_projection :
    ContMDiff 𝓘(ℝ) (𝓡 1) ∞ (fun t : ℝ => (t : AddCircle (2 * Real.pi))) := by
  convert contMDiff_angleCircleHomeomorph_symm.comp contMDiff_circleExp using 1
  funext t
  apply angleCircleHomeomorph.injective
  change angleCircleHomeomorph (t : AddCircle (2 * Real.pi)) =
    angleCircleHomeomorph (angleCircleHomeomorph.symm (Circle.exp t))
  rw [Homeomorph.apply_symm_apply]
  exact AddCircle.homeomorphCircle'_apply_mk t

theorem angleCircleHomeomorph_eq_toCircle (θ : AddCircle (2 * Real.pi)) :
    angleCircleHomeomorph θ = AddCircle.toCircle θ := by
  induction θ using QuotientAddGroup.induction_on
  simp [angleCircleHomeomorph, AddCircle.homeomorphCircle'_apply_mk,
    AddCircle.toCircle_apply_mk, Real.pi_ne_zero]

abbrev TorusCoordinates (n : ℕ) := Fin n → AngleModel

/-- The torus model is a real vector space of dimension `n`. -/
abbrev torusModel (n : ℕ) := 𝓘(ℝ, TorusCoordinates n)

instance torusChartedSpace (n : ℕ) : ChartedSpace (TorusCoordinates n) (Torus n) where
  atlas := OpenPartialHomeomorph.pi '' Set.pi Set.univ
    (fun _ : Fin n => atlas AngleModel (AddCircle (2 * Real.pi)))
  chartAt x := OpenPartialHomeomorph.pi (fun j => chartAt AngleModel (x j))
  mem_chart_source x := by intro j _; exact mem_chart_source _ _
  chart_mem_atlas x := ⟨_, (by intro j _; exact chart_mem_atlas _ _), rfl⟩

instance torusIsManifold (n : ℕ) : IsManifold (torusModel n) ∞ (Torus n) := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
  intro x hx
  apply contDiffWithinAt_pi.mpr
  intro j
  have hj := (contDiffGroupoid ∞ (𝓡 1)).compatible (he j (Set.mem_univ j))
    (he' j (Set.mem_univ j))
  have hmem : x j ∈ (e j).target ∧ (e j).symm (x j) ∈ (e' j).source :=
    ⟨hx.1.1 j (Set.mem_univ j), hx.1.2 j (Set.mem_univ j)⟩
  have hd := hj.1 (x j) ⟨hmem, ⟨x j, rfl⟩⟩
  exact hd.comp (f := fun y : TorusCoordinates n => y j) x
    (contDiff_apply ℝ AngleModel j).contDiffWithinAt (by
    intro y hy
    exact ⟨⟨hy.1.1 j (Set.mem_univ j), hy.1.2 j (Set.mem_univ j)⟩, ⟨y j, rfl⟩⟩)

/-- The logarithmic ambient uses the product of Euclidean and quotient atlases. -/
abbrev lgModel (n : ℕ) := (𝓘(ℝ, RealSpace n)).prod (torusModel n)

instance lgIsManifold (n : ℕ) : IsManifold (lgModel n) ∞ (LGSpace n) := inferInstance

/-- Coordinate evaluation is smooth for the finite product quotient atlas. -/
theorem contMDiff_torus_eval {n : ℕ} (j : Fin n) :
    ContMDiff (torusModel n) (𝓡 1) ∞ (fun θ : Torus n => θ j) := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨(continuous_apply j).continuousAt, ?_⟩
  let e := chartAt AngleModel (x j)
  have he : e (x j) ∈ e.target := e.map_source (mem_chart_source _ _)
  apply ContDiffAt.contDiffWithinAt
  apply (contDiff_apply ℝ AngleModel j).contDiffAt.congr_of_eventuallyEq
  have hn : {y : TorusCoordinates n | y j ∈ e.target} ∈
      𝓝 (extChartAt (torusModel n) x x) :=
    (e.open_target.preimage (continuous_apply j)).mem_nhds he
  filter_upwards [hn] with y hy
  exact e.right_inv hy

/-- The actual period-lattice projection is smooth, in every rank including zero. -/
theorem contMDiff_angleQuotient {n : ℕ} :
    ContMDiff 𝓘(ℝ, RealSpace n) (torusModel n) ∞ (angleQuotient (n := n)) := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨(continuous_pi (fun j => AddCircle.continuous_mk' _ |>.comp
    (continuous_apply j))).continuousAt, ?_⟩
  apply contDiffWithinAt_pi.mpr
  intro j
  have h := (contMDiffAt_iff.mp (contMDiff_angle_projection (x j))).2
  exact h.comp (f := fun y : RealSpace n => y j) x
    (contDiff_apply ℝ ℝ j).contDiffWithinAt (fun y _ => ⟨y j, rfl⟩)

/-- The additive integral character is the product of integer powers of the
coordinate unit-circle characters. -/
theorem character_eq_prod {n : ℕ} (v : Lattice n) (θ : Torus n) :
    character v θ = ∏ j, (angleCircleHomeomorph (θ j)) ^ (v j) := by
  classical
  unfold character integralAngle
  have h (s : Finset (Fin n)) :
      AddCircle.toCircle (∑ j ∈ s, v j • θ j) =
        ∏ j ∈ s, (angleCircleHomeomorph (θ j)) ^ (v j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finset.prod_insert ha, AddCircle.toCircle_add,
        AddCircle.toCircle_zsmul, ih, angleCircleHomeomorph_eq_toCircle]
  simpa using h Finset.univ

/-- Integral characters are smooth functions on the actual quotient torus. -/
theorem contMDiff_character {n : ℕ} (v : Lattice n) :
    ContMDiff (torusModel n) (𝓡 1) ∞ (character v) := by
  have hpow (j : Fin n) : ContMDiff (torusModel n) (𝓡 1) ∞
      (fun θ : Torus n => (angleCircleHomeomorph (θ j)) ^ (v j)) := by
    have h := contMDiff_angleCircleHomeomorph.comp (contMDiff_torus_eval j)
    cases hv : v j with
    | ofNat m => exact h.pow m
    | negSucc m => simpa only [zpow_negSucc, Function.comp_def] using (h.pow (m + 1)).inv
  have hc : character v = fun θ => ∏ j, (angleCircleHomeomorph (θ j)) ^ (v j) :=
    funext (character_eq_prod v)
  rw [hc]
  exact ContMDiff.prod (t := Finset.univ) (fun j _ => hpow j)

local instance complexRealContMDiffMul : ContMDiffMul 𝓘(ℝ, ℂ) ∞ ℂ where
  contMDiff_mul := by
    rw [contMDiff_iff]
    exact ⟨continuous_mul, fun _ _ => contDiff_mul.contDiffOn⟩

/-- Smoothness of a Laurent monomial on `Y`, using quotient characters. -/
theorem contMDiff_monomial {n : ℕ} (c : ℂ) (v : Lattice n) :
    ContMDiff (lgModel n) 𝓘(ℝ, ℂ) ∞ (monomial c v) := by
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  have hp : ContDiff ℝ ∞ (pairing v) := by unfold pairing; fun_prop
  have he : ContMDiff (lgModel n) 𝓘(ℝ, ℂ) ∞
      (fun y : LGSpace n => Complex.exp (pairing v y.1)) :=
    Complex.contDiff_exp.contMDiff.comp
      (Complex.ofRealCLM.contDiff.contMDiff.comp (hp.contMDiff.comp contMDiff_fst))
  have hc : ContMDiff (lgModel n) 𝓘(ℝ, ℂ) ∞
      (fun y : LGSpace n => (character v y.2 : ℂ)) :=
    (contMDiff_coe_sphere (E := ℂ) (n := 1)).comp
      ((contMDiff_character v).comp contMDiff_snd)
  exact (contMDiff_const.mul he).mul hc

/-- The specified superpotential is smooth on the quotient manifold itself. -/
theorem contMDiff_W {n : ℕ} (I : ToricInput n) :
    ContMDiff (lgModel n) 𝓘(ℝ, ℂ) ∞ (W I) := by
  unfold W
  exact ContMDiff.sum (fun v _ => contMDiff_monomial (I.coeff v) v.val)

end FsFltz
