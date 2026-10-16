import FsFltz.Geometry.SymplecticBridge
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Smooth local inverses for the quotient covers

The actual representative projections are smooth local diffeomorphisms.
The proof uses the finite-dimensional inverse function theorem in a target
chart, then transfers its inverse back to the quotient manifold.
This proves a quotient-coordinate foundation from `geoemtric-part-fsf.tex`,
`sec:data`, lines 57–97, and `sec:lean`, lines 778–814.
It does not assert the completion markings or comparison of `thm:target`,
lines 352–415.
-/

noncomputable section
open scoped Manifold ContDiff
open Topology

namespace FsFltz.Geometry
open SmoothManifold

/-- A smooth finite-dimensional representative map with everywhere bijective
derivative has smooth local inverses in the actual manifold atlas. -/
theorem isLocalDiffeomorph_of_bijective_mfderiv
    {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace M] [ChartedSpace F M]
    [IsManifold 𝓘(ℝ, F) ∞ M] {f : E → M}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hd : ∀ z, Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z)) :
    IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f := by
  intro a
  let c := chartAt F (f a)
  let g : E → F := c ∘ f
  have hcg (z : E) (hz : f z ∈ c.source) : ContDiffAt ℝ ∞ g z :=
    ((contMDiffOn_chart (I := 𝓘(ℝ, F)) (x := f a)).contMDiffAt
      (c.open_source.mem_nhds hz)).comp z (hf z) |>.contDiffAt
  have hgd (z : E) (hz : f z ∈ c.source) : Function.Bijective (fderiv ℝ g z) := by
    have hc := (mdifferentiable_chart (I := 𝓘(ℝ, F)) (f a)).mfderiv_bijective hz
    have he := mfderiv_comp z
      ((contMDiffOn_chart (I := 𝓘(ℝ, F)) (n := ∞) (x := f a)).contMDiffAt
        (c.open_source.mem_nhds hz) |>.mdifferentiableAt (by simp))
      (hf.mdifferentiable (by simp) z)
    rw [mfderiv_eq_fderiv] at he
    rw [he]
    exact hc.comp (hd z)
  let d (z : E) (hz : f z ∈ c.source) : E ≃L[ℝ] F :=
    (LinearEquiv.ofBijective (fderiv ℝ g z).toLinearMap (hgd z hz)).toContinuousLinearEquiv
  have hder (z : E) (hz : f z ∈ c.source) : HasFDerivAt g (d z hz : E →L[ℝ] F) z := by
    exact (hcg z hz).differentiableAt (by simp) |>.hasFDerivAt
  have ha : f a ∈ c.source := mem_chart_source F (f a)
  let e₀ := (hcg a ha).toOpenPartialHomeomorph g (hder a ha) (by simp)
  let e := e₀.restrOpen (f ⁻¹' c.source) (c.open_source.preimage hf.continuous)
  let t := e.trans c.symm
  have heq : Set.EqOn f t t.source := by
    intro z hz
    have hz' : f z ∈ c.source := hz.1.2
    exact (c.left_inv hz').symm
  refine ⟨{ t.toPartialEquiv with
      open_source := t.open_source
      open_target := t.open_target
      contMDiffOn_toFun := hf.contMDiffOn.congr heq.symm
      contMDiffOn_invFun := ?_ }, ?_, heq⟩
  · intro y hy
    have hcy : c y ∈ e.target := hy.2
    have hcy₀ : c y ∈ e₀.target := hcy.1
    have hz : f (e₀.symm (c y)) ∈ c.source := hcy.2
    have hinv : ContDiffAt ℝ ∞ e₀.symm (c y) :=
      e₀.contDiffAt_symm hcy₀ (hder _ hz) (hcg _ hz)
    exact (hinv.contMDiffAt.comp y
      ((contMDiffOn_chart (I := 𝓘(ℝ, F)) (x := f a)).contMDiffAt
        (c.open_source.mem_nhds hy.1))).contMDiffWithinAt
  · change a ∈ e.source ∧ e a ∈ c.target
    exact ⟨⟨(hcg a ha).mem_toOpenPartialHomeomorph_source (hder a ha) (by simp), ha⟩,
      c.map_source ha⟩

/-- The actual logarithmic quotient cover is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_lgCover (n : ℕ) :
    IsLocalDiffeomorph 𝓘(ℝ, TangentCoordinates n) 𝓘(ℝ, Model (2 * n)) ∞
      (lgCover (n := n)) :=
  isLocalDiffeomorph_of_bijective_mfderiv (contMDiff_lgCover n) lgCoverTangent_bijective

/-- The actual cotangent quotient cover is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_cotangentCover (n : ℕ) :
    IsLocalDiffeomorph 𝓘(ℝ, TangentCoordinates n) 𝓘(ℝ, Model (2 * n)) ∞
      (cotangentCover (n := n)) :=
  isLocalDiffeomorph_of_bijective_mfderiv
    (contMDiff_cotangentCover n) cotangentCoverTangent_bijective

/-- Smoothness of a quotient function can be tested through a local cover.
The reverse implication uses the smooth local inverse and its right inverse
identity on a neighborhood, rather than only an invertible tangent map. -/
theorem contMDiffAt_iff_comp_of_isLocalDiffeomorphAt
    {E F G M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace F M] {f : E → M} {a : E}
    (hf : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f a) (h : M → G) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ h (f a) ↔
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ (h ∘ f) a := by
  constructor
  · intro hh
    exact hh.comp a hf.contMDiffAt
  · intro hh
    have ha : hf.localInverse (f a) = a :=
      hf.localInverse_left_inv hf.localInverse_mem_target
    have hi := hf.localInverse_contMDiffAt
    have hh' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ (h ∘ f)
        (hf.localInverse (f a)) := by
      rw [ha]
      exact hh
    apply (hh'.comp (f a) hi).congr_of_eventuallyEq
    filter_upwards [hf.localInverse_eventuallyEq_right] with y hy
    exact congrArg h hy.symm

/-- A function on the actual LG quotient is smooth exactly when its full
representative-coordinate formula is smooth. -/
theorem contMDiff_iff_contDiff_lgCover {n : ℕ} {G : Type}
    [NormedAddCommGroup G] [NormedSpace ℝ G] (h : (lgManifold n).Point → G) :
    ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, G) ∞ h ↔
      ContDiff ℝ ∞ (h ∘ lgCover) := by
  constructor
  · intro hh
    exact (hh.comp (contMDiff_lgCover n)).contDiff
  · intro hh y
    obtain ⟨x, rfl⟩ := lgCover_surjective n y
    exact (contMDiffAt_iff_comp_of_isLocalDiffeomorphAt
      (isLocalDiffeomorph_lgCover n x) h).mpr (hh.contMDiff x)

/-- The analogous smoothness transfer uses the endpoint's angular/momentum
order on the actual cotangent quotient. -/
theorem contMDiff_iff_contDiff_cotangentCover {n : ℕ} {G : Type}
    [NormedAddCommGroup G] [NormedSpace ℝ G] (h : (cotangentManifold n).Point → G) :
    ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, G) ∞ h ↔
      ContDiff ℝ ∞ (h ∘ cotangentCover) := by
  constructor
  · intro hh
    exact (hh.comp (contMDiff_cotangentCover n)).contDiff
  · intro hh y
    obtain ⟨x, rfl⟩ := cotangentCover_surjective n y
    exact (contMDiffAt_iff_comp_of_isLocalDiffeomorphAt
      (isLocalDiffeomorph_cotangentCover n x) h).mpr (hh.contMDiff x)

end FsFltz.Geometry
