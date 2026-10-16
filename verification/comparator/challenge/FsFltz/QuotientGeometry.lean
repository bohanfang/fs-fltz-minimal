import FsFltz.SmoothTorus
import FsFltz.Geometry.Smooth

/-!
# Euclidean presentations of the quotient endpoints

The actual quotient atlas from `SmoothTorus` is transported by a continuous
linear change of model. This supplies concrete extension manifolds for the
endpoints in `sec:data`, lines 57–94 of `geoemtric-part-fsf.tex`, without
changing either endpoint's points or topology. The differential-form and
tangent-coordinate correspondence in `sec:lean`, lines 805–814, is separate.
-/

noncomputable section
open scoped Manifold ContDiff
open Topology

namespace FsFltz

section Rechart

variable {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
  [ChartedSpace E M] (c : E ≃L[ℝ] F)

/-- Change only the linear model of an atlas. -/
@[instance_reducible]
def linearRechart : ChartedSpace F M where
  atlas := {e.transHomeomorph c.toHomeomorph | e ∈ atlas E M}
  chartAt x := (chartAt E x).transHomeomorph c.toHomeomorph
  mem_chart_source x := mem_chart_source E x
  chart_mem_atlas _x := ⟨_, chart_mem_atlas _ _, rfl⟩

theorem linearRechart_isManifold [IsManifold 𝓘(ℝ, E) ∞ M] :
    @IsManifold ℝ _ F _ _ F _ 𝓘(ℝ, F) ∞ M _ (linearRechart (M := M) c) := by
  let := linearRechart (M := M) c
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
  have h := (contDiffGroupoid ∞ 𝓘(ℝ, E)).compatible he he'
  have hd : ContDiffOn ℝ ∞ (fun x => e' (e.symm x))
      (e.target ∩ e.symm ⁻¹' e'.source) := by
    have hd' := h.1
    change ContDiffOn ℝ ∞ (𝓘(ℝ, E) ∘ e.symm.trans e' ∘ 𝓘(ℝ, E).symm)
      (𝓘(ℝ, E).symm ⁻¹' (e.symm.trans e').source ∩ Set.range 𝓘(ℝ, E)) at hd'
    simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_def, Set.preimage_id, Set.range_id, Set.inter_univ, id_eq,
      OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source] using hd'
  apply c.contDiff.comp_contDiffOn
  apply hd.comp c.symm.contDiff.contDiffOn
  intro x hx
  exact hx.1

theorem contMDiff_linearRechart_id [IsManifold 𝓘(ℝ, E) ∞ M] :
    @ContMDiff ℝ _ E _ _ E _ 𝓘(ℝ, E) M _ ‹ChartedSpace E M›
      F _ _ F _ 𝓘(ℝ, F) M _ (linearRechart (M := M) c) ∞ id := by
  let := linearRechart (M := M) c
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuousAt_id, ?_⟩
  let e := chartAt E x
  have he : e x ∈ e.target := e.map_source (mem_chart_source E x)
  apply ContDiffAt.contDiffWithinAt
  apply c.contDiff.contDiffAt.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds he] with y hy
  change c (e (e.symm y)) = c y
  rw [e.right_inv hy]

theorem contMDiff_linearRechart_id_symm [IsManifold 𝓘(ℝ, E) ∞ M] :
    @ContMDiff ℝ _ F _ _ F _ 𝓘(ℝ, F) M _ (linearRechart (M := M) c)
      E _ _ E _ 𝓘(ℝ, E) M _ ‹ChartedSpace E M› ∞ id := by
  let := linearRechart (M := M) c
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuousAt_id, ?_⟩
  let e := chartAt E x
  have he : e x ∈ e.target := e.map_source (mem_chart_source E x)
  apply ContDiffAt.contDiffWithinAt
  apply c.symm.contDiff.contDiffAt.congr_of_eventuallyEq
  have hn : c.symm ⁻¹' e.target ∈ 𝓝 (c (e x)) :=
    (e.open_target.preimage c.symm.continuous).mem_nhds (by simpa using he)
  filter_upwards [hn] with y hy
  change e (e.symm (c.symm y)) = c.symm y
  exact e.right_inv hy

/-- The atlas change is an actual smooth diffeomorphism, with identity point map. -/
def linearRechartDiffeomorph [IsManifold 𝓘(ℝ, E) ∞ M] :
    letI := linearRechart (M := M) c
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M M ∞ := by
  letI := linearRechart (M := M) c
  exact { toEquiv := Equiv.refl M
          contMDiff_toFun := contMDiff_linearRechart_id c
          contMDiff_invFun := contMDiff_linearRechart_id_symm c }

end Rechart

abbrev LGCoordinates (n : ℕ) := RealSpace n × TorusCoordinates n
abbrev CotangentCoordinates (n : ℕ) := TorusCoordinates n × RealSpace n

instance lgChartedSpaceSelf (n : ℕ) : ChartedSpace (LGCoordinates n) (LGSpace n) :=
  inferInstanceAs (ChartedSpace (ModelProd (RealSpace n) (TorusCoordinates n)) (LGSpace n))

instance cotangentChartedSpaceSelf (n : ℕ) :
    ChartedSpace (CotangentCoordinates n) (Cotangent n) :=
  inferInstanceAs (ChartedSpace (ModelProd (TorusCoordinates n) (RealSpace n)) (Cotangent n))

instance lgIsManifoldSelf (n : ℕ) : IsManifold 𝓘(ℝ, LGCoordinates n) ∞ (LGSpace n) where
  compatible := by
    intro e e' he he'
    exact (contDiffGroupoid ∞ (lgModel n)).compatible he he'

instance cotangentIsManifoldSelf (n : ℕ) :
    IsManifold 𝓘(ℝ, CotangentCoordinates n) ∞ (Cotangent n) where
  compatible := by
    intro e e' he he'
    exact (contDiffGroupoid ∞ ((torusModel n).prod 𝓘(ℝ, RealSpace n))).compatible he he'

def lgEuclideanEquiv (n : ℕ) : LGCoordinates n ≃L[ℝ] Geometry.Model (2 * n) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    simp [LGCoordinates, RealSpace, TorusCoordinates, AngleModel, Geometry.Model,
      Module.finrank_prod, Module.finrank_pi_fintype, finrank_euclideanSpace, two_mul])

def cotangentEuclideanEquiv (n : ℕ) :
    CotangentCoordinates n ≃L[ℝ] Geometry.Model (2 * n) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    simp [CotangentCoordinates, RealSpace, TorusCoordinates, AngleModel, Geometry.Model,
      Module.finrank_prod, Module.finrank_pi_fintype, finrank_euclideanSpace, two_mul])

/-- `Y` itself, with the quotient atlas in a Euclidean model. -/
def lgManifold (n : ℕ) : Geometry.SmoothManifold (2 * n) where
  Point := LGSpace n
  topology := inferInstance
  charts := linearRechart (M := LGSpace n) (lgEuclideanEquiv n)
  hausdorff := inferInstance
  secondCountable := inferInstance
  smooth := linearRechart_isManifold (M := LGSpace n) (lgEuclideanEquiv n)

/-- The based cotangent endpoint itself, with the same quotient torus topology. -/
def cotangentManifold (n : ℕ) : Geometry.SmoothManifold (2 * n) where
  Point := Cotangent n
  topology := inferInstance
  charts := linearRechart (M := Cotangent n) (cotangentEuclideanEquiv n)
  hausdorff := inferInstance
  secondCountable := inferInstance
  smooth := linearRechart_isManifold (M := Cotangent n) (cotangentEuclideanEquiv n)

def lgQuotientDiffeomorph (n : ℕ) :
    letI : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
    Diffeomorph 𝓘(ℝ, LGCoordinates n) 𝓘(ℝ, Geometry.Model (2 * n))
      (LGSpace n) (lgManifold n).Point ∞ :=
  linearRechartDiffeomorph (M := LGSpace n) (lgEuclideanEquiv n)

def cotangentQuotientDiffeomorph (n : ℕ) :
    letI : ChartedSpace (Geometry.Model (2 * n)) (Cotangent n) := (cotangentManifold n).charts
    Diffeomorph 𝓘(ℝ, CotangentCoordinates n) 𝓘(ℝ, Geometry.Model (2 * n))
      (Cotangent n) (cotangentManifold n).Point ∞ :=
  linearRechartDiffeomorph (M := Cotangent n) (cotangentEuclideanEquiv n)

/-- Smoothness survives the Euclidean change of model used by geometric forms. -/
theorem contMDiff_W_lgManifold {n : ℕ} (I : ToricInput n) :
    letI : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
    ContMDiff 𝓘(ℝ, Geometry.Model (2 * n)) 𝓘(ℝ, ℂ) ∞
      (fun y : (lgManifold n).Point => W I y) := by
  let : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  exact (contMDiff_W I).comp
    (contMDiff_linearRechart_id_symm (M := LGSpace n) (lgEuclideanEquiv n))

set_option backward.isDefEq.respectTransparency false in
theorem contMDiff_lg_circleCoordinate {n : ℕ} (j : Fin n) :
    letI : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
    ContMDiff 𝓘(ℝ, Geometry.Model (2 * n)) 𝓘(ℝ, ℂ) ∞
      (fun y : (lgManifold n).Point => (AddCircle.toCircle (y.2 j) : ℂ)) := by
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  let : ChartedSpace (Geometry.Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have h := (contMDiff_angleCircleHomeomorph.comp (contMDiff_torus_eval j)).comp
    (contMDiff_snd : ContMDiff (lgModel n) (torusModel n) ∞ (Prod.snd : LGSpace n → _))
  have hc := (contMDiff_coe_sphere (E := ℂ) (n := 1)).comp h
  simpa [Function.comp_def, angleCircleHomeomorph_eq_toCircle, lgManifold] using hc.comp
    (contMDiff_linearRechart_id_symm (M := LGSpace n) (lgEuclideanEquiv n))

set_option backward.isDefEq.respectTransparency false in
theorem contMDiff_cotangent_circleCoordinate {n : ℕ} (j : Fin n) :
    letI : ChartedSpace (Geometry.Model (2 * n)) (Cotangent n) := (cotangentManifold n).charts
    ContMDiff 𝓘(ℝ, Geometry.Model (2 * n)) 𝓘(ℝ, ℂ) ∞
      (fun y : (cotangentManifold n).Point => (AddCircle.toCircle (y.1 j) : ℂ)) := by
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  let : ChartedSpace (Geometry.Model (2 * n)) (Cotangent n) := (cotangentManifold n).charts
  have h := (contMDiff_angleCircleHomeomorph.comp (contMDiff_torus_eval j)).comp
    (contMDiff_fst : ContMDiff ((torusModel n).prod 𝓘(ℝ, RealSpace n)) (torusModel n) ∞
      (Prod.fst : Cotangent n → _))
  have hc := (contMDiff_coe_sphere (E := ℂ) (n := 1)).comp h
  simpa [Function.comp_def, angleCircleHomeomorph_eq_toCircle, cotangentManifold] using hc.comp
    (contMDiff_linearRechart_id_symm (M := Cotangent n) (cotangentEuclideanEquiv n))

end FsFltz
