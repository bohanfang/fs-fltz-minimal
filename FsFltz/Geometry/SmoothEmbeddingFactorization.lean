import FsFltz.Geometry.LocalInverse
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Smooth factorization through an actual embedded submanifold

Source: `geoemtric-part-fsf.tex`, `g:initial`, lines 373–384, and
`sec:lean`, lines 783–814; `geometric-part-fsf-proof.tex`,
`prop:allinitial`, lines 923–938.
An ambient smooth embedding with image inside another actual embedded
submanifold factors through it by a smooth embedding. The topological lift
is continuous, and projection onto the first embedding's injective tangent
image supplies a local inverse proving its smoothness. No smooth lift is
assumed.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter Function

namespace FsFltz.Geometry
open SmoothManifold

/-- A continuous map into an actual embedded submanifold is smooth whenever
its ambient composition is smooth. A tangent left inverse and the native
inverse function theorem construct the local smooth lift. -/
theorem contMDiff_of_comp_smoothEmbedding {dN dP dM : ℕ}
    (N : SmoothManifold dN) (P : SmoothManifold dP) (M : SmoothManifold dM)
    (i : N.SmoothEmbedding M) {q : P.Point → N.Point} (hq : Continuous q)
    (hcomp : ContMDiff 𝓘(ℝ, Model dP) 𝓘(ℝ, Model dM) ∞ (i.map ∘ q)) :
    ContMDiff 𝓘(ℝ, Model dP) 𝓘(ℝ, Model dN) ∞ q := by
  intro x
  let a := q x
  let c := chartAt (Model dM) (i.map a)
  let J : Model dN →L[ℝ] Model dM :=
    mfderiv 𝓘(ℝ, Model dN) 𝓘(ℝ, Model dM) i.map a
  obtain ⟨l, hl⟩ := J.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (i.immersion a))
  let L : Model dM →L[ℝ] Model dN := l.toContinuousLinearMap
  let h : N.Point → Model dN := L ∘ c ∘ i.map
  let U : Set N.Point := i.map ⁻¹' c.source
  have hU : IsOpen U := c.open_source.preimage i.map.contMDiff.continuous
  have haU : a ∈ U := mem_chart_source _ _
  have hcs : ContMDiffOn 𝓘(ℝ, Model dM) 𝓘(ℝ, Model dM) ∞ c c.source :=
    contMDiffOn_chart
  have hhs : ContMDiffOn 𝓘(ℝ, Model dN) 𝓘(ℝ, Model dN) ∞ h U :=
    L.contMDiff.comp_contMDiffOn
      (hcs.comp i.map.contMDiff.contMDiffOn (fun y hy => hy))
  have hca := (hcs.contMDiffAt (c.open_source.mem_nhds haU)).mdifferentiableAt (by simp)
  have hia := i.map.contMDiff.mdifferentiableAt (x := a) (by simp)
  have hcder : mfderiv 𝓘(ℝ, Model dM) 𝓘(ℝ, Model dM) c (i.map a) =
      ContinuousLinearMap.id ℝ (Model dM) := by
    exact mfderiv_extChartAt_self (I := 𝓘(ℝ, Model dM))
  have hhd : mfderiv 𝓘(ℝ, Model dN) 𝓘(ℝ, Model dN) h a =
      ContinuousLinearMap.id ℝ (Model dN) := by
    rw [mfderiv_comp a L.hasMFDerivAt.mdifferentiableAt (hca.comp a hia),
      L.hasMFDerivAt.mfderiv, mfderiv_comp a hca hia, hcder]
    ext v
    change l (J v) = v
    exact congrArg (fun A : Model dN →ₗ[ℝ] Model dN => A v) hl
  obtain ⟨e, hae, he⟩ := isLocalDiffeomorphAt_of_bijective_mfderiv_manifold
    hU hhs haU (by rw [hhd]; exact Function.bijective_id)
  have hqsource : ∀ᶠ y in 𝓝 x, q y ∈ e.source :=
    hq.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hae)
  have hcx : ContMDiffAt 𝓘(ℝ, Model dP) 𝓘(ℝ, Model dM) ∞
      (c ∘ i.map ∘ q) x :=
    (hcs.contMDiffAt (c.open_source.mem_nhds haU)).comp x hcomp.contMDiffAt
  have hproj : ContMDiffAt 𝓘(ℝ, Model dP) 𝓘(ℝ, Model dN) ∞
      (h ∘ q) x := L.contMDiff.contMDiffAt.comp x hcx
  have htarget : h (q x) ∈ e.target := by
    rw [he hae]
    exact e.map_source hae
  have hinv := e.contMDiffOn_invFun.contMDiffAt (e.open_target.mem_nhds htarget)
  apply (hinv.comp x hproj).congr_of_eventuallyEq
  filter_upwards [hqsource] with y hy
  change q y = e.symm (h (q y))
  rw [he hy]
  exact (e.left_inv hy).symm

/-- A smooth ambient embedding whose image lies in another actual smoothly
embedded submanifold factors through it by an actual smooth embedding.
Continuity of the range lift follows from the induced topology, smoothness
from the tangent left-inverse local construction, and immersion from the
ambient differential chain rule. -/
theorem exists_smoothEmbedding_factor {dN dP dM : ℕ}
    (N : SmoothManifold dN) (P : SmoothManifold dP) (M : SmoothManifold dM)
    (i : N.SmoothEmbedding M) (g : P.SmoothEmbedding M)
    (hrange : Set.range g.map ⊆ Set.range i.map) :
    ∃ q : P.SmoothEmbedding N, ∀ x, i.map (q.map x) = g.map x := by
  have hpre (x : P.Point) : ∃ y : N.Point, i.map y = g.map x :=
    hrange ⟨x, rfl⟩
  choose q hqeq using hpre
  have hcomp : i.map ∘ q = g.map := funext hqeq
  have hqcont : Continuous q := i.embedding.isInducing.continuous_iff.mpr (by
    rw [hcomp]
    exact g.map.contMDiff.continuous)
  have hqsmooth : ContMDiff 𝓘(ℝ, Model dP) 𝓘(ℝ, Model dN) ∞ q :=
    contMDiff_of_comp_smoothEmbedding N P M i hqcont (by
      rw [hcomp]
      exact g.map.contMDiff)
  have hqembedding : Topology.IsEmbedding q := i.embedding.of_comp_iff.mp (by
    rw [hcomp]
    exact g.embedding)
  have hqimmersion (x : P.Point) : Function.Injective
      (mfderiv 𝓘(ℝ, Model dP) 𝓘(ℝ, Model dN) q x) := by
    have hchain := mfderiv_comp (f := q) (g := i.map) x
      (i.map.contMDiff.mdifferentiableAt (by simp))
      (hqsmooth.mdifferentiableAt (by simp))
    rw [hcomp] at hchain
    intro v w hvw
    apply g.immersion x
    rw [hchain]
    exact congrArg (mfderiv 𝓘(ℝ, Model dN) 𝓘(ℝ, Model dM) i.map (q x)) hvw
  exact ⟨{ map := ⟨q, hqsmooth⟩, embedding := hqembedding, immersion := hqimmersion }, hqeq⟩

end FsFltz.Geometry
