import FsFltz.Geometry.CollarExtension
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

/-!
# Native integration and uniqueness for the supported collar velocity

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–189, and `sec:lean`,
lines 788–814. A time-dependent field is replaced by the autonomous field
`(1, Z)` on the product of time with the boundaryless extension manifold.
Native local existence gives actual spatial solutions. Native uniqueness
recovers the prescribed collar interpolation and the stationary boundary
curves from their initial values whenever the compared solution is defined
on the stated open time interval; agreement concerns the full smaller
collar, including both endpoints of the closed parameter interval.

For local existence, the first coordinate of a suspended solution has
derivative one and prescribed initial value, hence equals the real time
coordinate by uniqueness for that scalar equation. Its second coordinate
therefore solves the original time-dependent equation. Two spatial
solutions lift to integral curves of the same suspended field, so native
uniqueness applies. The constructed open time margin contains `[0,1]`,
placing the initial time zero in its interior. Constant spatial curves
solve the equation at boundary points and outside the spatial projection
of the support; uniqueness forces any compared solution to stay constant.

These results do not construct a smooth family of global diffeomorphisms.
`CollarEvolution` derives neighborhood-uniform local lifetimes and uses
compactness and native continuation to construct all-real solutions and
invertible evolution maps for this actual field. Joint smooth dependence
on initial points, and hence smooth evolution and inverse maps, remains
pending. These foundations do not establish the geometric target
`thm:target` (lines 361–429).
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology

namespace FsFltz.Geometry
open SmoothManifold

namespace CollarFlow

variable {F Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace Q] [ChartedSpace F Q] [IsManifold 𝓘(ℝ, F) ∞ Q]

/-- The autonomous field whose integral curves have time coordinate of
speed one and spatial coordinate governed by the actual supplied field. -/
def timeSuspension (Z : ℝ → (x : Q) → TangentSpace 𝓘(ℝ, F) x)
    (p : ℝ × Q) : TangentSpace ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) p :=
  (1, Z p.1 p.2)

theorem contMDiff_timeSuspension
    {Z : ℝ → (x : Q) → TangentSpace 𝓘(ℝ, F) x}
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ((𝓘(ℝ, F)).tangent) ∞
      (fun p : ℝ × Q => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, F) Q))) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F))
      (((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)).tangent) ∞
      (fun p : ℝ × Q => (⟨p, timeSuspension Z p⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) (ℝ × Q))) := by
  have ht : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).tangent) ∞
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  exact contMDiff_equivTangentBundleProd_symm.comp
    ((ht.comp contMDiff_fst).prodMk hZ)

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold 𝓘(ℝ, F) ∞ Q] in
/-- The spatial ODE is exactly the native integral-curve equation after
adjoining its real time coordinate. -/
theorem hasMFDerivAt_lift
    {Z : ℝ → (x : Q) → TangentSpace 𝓘(ℝ, F) x} {γ : ℝ → Q} {t : ℝ}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t)))) :
    HasMFDerivAt 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F))
      (fun s => (s, γ s)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (timeSuspension Z (t, γ t))) := by
  apply ((hasMFDerivAt_id t).prodMk hγ).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  change (r, r • Z t (γ t)) = r • ((1 : ℝ), Z t (γ t))
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Solutions of the nonautonomous native ODE agree on their common open
time interval once their initial spatial values agree. -/
theorem eqOn_of_hasMFDerivAt [T2Space Q]
    {Z : ℝ → (x : Q) → TangentSpace 𝓘(ℝ, F) x}
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ((𝓘(ℝ, F)).tangent) ∞
      (fun p : ℝ × Q => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, F) Q)))
    {γ γ' : ℝ → Q} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hγ : ∀ t ∈ Ioo a b, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t))))
    (hγ' : ∀ t ∈ Ioo a b, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ' t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ' t))))
    (heq : γ t₀ = γ' t₀) : EqOn γ γ' (Ioo a b) := by
  have hleft : IsMIntegralCurveOn (fun t => (t, γ t)) (timeSuspension Z) (Ioo a b) :=
    fun t ht => (hasMFDerivAt_lift (hγ t ht)).hasMFDerivWithinAt
  have hright : IsMIntegralCurveOn (fun t => (t, γ' t)) (timeSuspension Z) (Ioo a b) :=
    fun t ht => (hasMFDerivAt_lift (hγ' t ht)).hasMFDerivWithinAt
  have h := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht₀
    ((contMDiff_timeSuspension hZ).of_le (by simp)) hleft hright (by simp only [heq])
  intro t ht
  exact congrArg Prod.snd (h ht)

set_option backward.isDefEq.respectTransparency false in
/-- The suspended local integral curve gives a genuine local solution of
the original nonautonomous equation through every prescribed spacetime
point. No solution or family is included among the hypotheses. -/
theorem exists_local_solution [CompleteSpace F]
    {Z : ℝ → (x : Q) → TangentSpace 𝓘(ℝ, F) x}
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ((𝓘(ℝ, F)).tangent) ∞
      (fun p : ℝ × Q => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, F) Q)))
    (t₀ : ℝ) (x₀ : Q) :
    ∃ γ : ℝ → Q, γ t₀ = x₀ ∧
      ∀ᶠ t in 𝓝 t₀, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t))) := by
  obtain ⟨α, hα₀, hα⟩ := exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
    (x₀ := (t₀, x₀)) t₀
    (((contMDiff_timeSuspension hZ).of_le (by simp)) (t₀, x₀))
  have htime : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun s => (α s).1) (1 : ℝ) t := by
    filter_upwards [hα] with t ht
    have hf := (hasMFDerivAt_fst (α t)).comp t ht
    have hd := (hasMFDerivAt_iff_hasFDerivAt.mp hf).hasDerivAt
    apply hd.congr_deriv
    change (1 : ℝ) • (1 : ℝ) = 1
    simp
  have htimeEq : (fun s => (α s).1) =ᶠ[𝓝 t₀] id := by
    apply ODE_solution_unique_of_eventually
      (v := fun (_ : ℝ) (_ : ℝ) => (1 : ℝ)) (s := fun _ => univ)
      (K := 0) (Filter.Eventually.of_forall (fun _ => (LipschitzWith.const 1).lipschitzOnWith))
    · exact htime.mono (fun _ ht => ⟨ht, mem_univ _⟩)
    · exact Filter.Eventually.of_forall (fun t => ⟨hasDerivAt_id t, mem_univ _⟩)
    · exact congrArg Prod.fst hα₀
  refine ⟨fun t => (α t).2, congrArg Prod.snd hα₀, ?_⟩
  filter_upwards [hα, htimeEq] with t ht he
  have hs := (hasMFDerivAt_snd (α t)).comp t ht
  apply hs.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  simp [timeSuspension, he]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A point at which the time-dependent field vanishes throughout an open
time interval is stationary for every solution with that initial value. -/
theorem eqOn_const_of_hasMFDerivAt [T2Space Q]
    {Z : ℝ → (x : Q) → TangentSpace 𝓘(ℝ, F) x}
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ((𝓘(ℝ, F)).tangent) ∞
      (fun p : ℝ × Q => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, F) Q)))
    {γ : ℝ → Q} {a b t₀ : ℝ} {x : Q} (ht₀ : t₀ ∈ Ioo a b)
    (hzero : ∀ t ∈ Ioo a b, Z t x = 0)
    (hγ : ∀ t ∈ Ioo a b, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t))))
    (heq : γ t₀ = x) : EqOn γ (fun _ => x) (Ioo a b) := by
  apply eqOn_of_hasMFDerivAt hZ ht₀ hγ _ heq
  intro t ht
  rw [hzero t ht]
  simpa only [ContinuousLinearMap.smulRight_zero] using
    (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, F)) x t)

/-- Outside the spatial projection of the compact spacetime support, the
field vanishes at all times, so solutions are stationary there. -/
theorem eqOn_const_of_notMem_spatialSupport [T2Space Q]
    {Z : ℝ → (x : Q) → TangentSpace 𝓘(ℝ, F) x}
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ((𝓘(ℝ, F)).tangent) ∞
      (fun p : ℝ × Q => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, F) Q)))
    {K : Set (ℝ × Q)} (hzero : ∀ p ∉ K, Z p.1 p.2 = 0)
    {γ : ℝ → Q} {a b t₀ : ℝ} {x : Q} (ht₀ : t₀ ∈ Ioo a b)
    (hx : x ∉ Prod.snd '' K)
    (hγ : ∀ t ∈ Ioo a b, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t))))
    (heq : γ t₀ = x) : EqOn γ (fun _ => x) (Ioo a b) := by
  apply eqOn_const_of_hasMFDerivAt hZ ht₀ _ hγ heq
  intro t _
  exact hzero (t, x) (fun htx => hx ⟨(t, x), htx, rfl⟩)

end CollarFlow

namespace Completion

variable {d : ℕ} {D E : LiouvilleDomain d} (C : Completion D) (C' : Completion E)
  (h : DomainPresentationEquiv D.domain E.domain)

/-- Native uniqueness recovers the prescribed interpolation on every point
of the full smaller collar and at both closed-interval endpoints. -/
theorem eqOn_collarInterpolation_of_hasMFDerivAt
    {Z : ℝ → (x : E.domain.extension.Point) → E.domain.extension.Tangent x}
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ((𝓘(ℝ, Model d)).tangent) ∞
      (fun p : ℝ × E.domain.extension.Point =>
        (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) E.domain.extension.Point)))
    {ε δ : ℝ} (hε : 0 < ε)
    (hode : ∀ t ∈ Ioo (-ε) (1 + ε), ∀ q ∈ univ ×ˢ Ioo (-δ) δ,
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
        (fun s => C.compactPresentationInterpolation C' h (s, q)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (Z t (C.compactPresentationInterpolation C' h (t, q)))))
    {q : D.domain.boundary.Point × ℝ} (hq : q ∈ univ ×ˢ Ioo (-δ) δ)
    {γ : ℝ → E.domain.extension.Point}
    (hγ : ∀ t ∈ Ioo (-ε) (1 + ε), HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t))))
    (heq : γ 0 = C.compactPresentationInterpolation C' h (0, q)) :
    EqOn γ (fun t => C.compactPresentationInterpolation C' h (t, q)) (Icc (0 : ℝ) 1) := by
  have hcmp := CollarFlow.eqOn_of_hasMFDerivAt hZ
    (t₀ := 0) (show (0 : ℝ) ∈ Ioo (-ε) (1 + ε) by constructor <;> linarith)
    hγ (fun t ht => hode t ht q hq) heq
  intro t ht
  exact hcmp ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Boundary vanishing of the constructed field becomes pointwise boundary
fixing for its solutions, by actual ODE uniqueness. -/
theorem eqOn_boundary_of_hasMFDerivAt
    {Z : ℝ → (x : E.domain.extension.Point) → E.domain.extension.Tangent x}
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ((𝓘(ℝ, Model d)).tangent) ∞
      (fun p : ℝ × E.domain.extension.Point =>
        (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) E.domain.extension.Point)))
    (hboundary : ∀ (t : ℝ) (x : E.domain.boundary.Point),
      Z t (E.domain.boundaryInclusion.map x) = 0)
    {γ : ℝ → E.domain.extension.Point} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) (x : E.domain.boundary.Point)
    (hγ : ∀ t ∈ Ioo a b, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t))))
    (heq : γ t₀ = E.domain.boundaryInclusion.map x) :
    EqOn γ (fun _ => E.domain.boundaryInclusion.map x) (Ioo a b) :=
  CollarFlow.eqOn_const_of_hasMFDerivAt hZ ht₀ (fun t _ => hboundary t x) hγ heq

/-- The actual cutoff construction supplies native local solutions through
every point. Every solution on its open parameter interval which starts at
a collar point is forced to be the supplied interpolation on the full
smaller collar. This is a local integration producer, with no global
evolution or diffeomorphism family assumed or concluded. -/
theorem exists_collarVelocity_localSolutions :
    ∃ (ε : ℝ), 0 < ε ∧ ∃ (δ : ℝ), 0 < δ ∧
      ∃ (Z : ℝ → (x : E.domain.extension.Point) → E.domain.extension.Tangent x)
        (K : Set (ℝ × E.domain.extension.Point)),
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ((𝓘(ℝ, Model d)).tangent) ∞
        (fun p : ℝ × E.domain.extension.Point =>
          (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) E.domain.extension.Point)) ∧
      IsCompact K ∧ (∀ p ∉ K, Z p.1 p.2 = 0) ∧
      (∀ (t : ℝ) (x : E.domain.boundary.Point), Z t (E.domain.boundaryInclusion.map x) = 0) ∧
      (∀ t ∈ Ioo (-ε) (1 + ε), ∀ q ∈ univ ×ˢ Ioo (-δ) δ,
        HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
          (fun s => C.compactPresentationInterpolation C' h (s, q)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (Z t (C.compactPresentationInterpolation C' h (t, q))))) ∧
      (∀ (t₀ : ℝ) (x₀ : E.domain.extension.Point),
        ∃ γ : ℝ → E.domain.extension.Point, γ t₀ = x₀ ∧
          ∀ᶠ t in 𝓝 t₀, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t)))) ∧
      ∀ q ∈ univ ×ˢ Ioo (-δ) δ, ∀ γ : ℝ → E.domain.extension.Point,
        (∀ t ∈ Ioo (-ε) (1 + ε), HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) γ t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t)))) →
        γ 0 = C.compactPresentationInterpolation C' h (0, q) →
        EqOn γ (fun t => C.compactPresentationInterpolation C' h (t, q)) (Icc (0 : ℝ) 1) := by
  obtain ⟨ε, hε, δ, hδ, Z, K, hZ, hK, hzero, hboundary, hode⟩ :=
    C.exists_compactlySupported_collarVelocity_open_time C' h
  refine ⟨ε, hε, δ, hδ, Z, K, hZ, hK, hzero, hboundary, hode, ?_, ?_⟩
  · exact CollarFlow.exists_local_solution hZ
  · intro q hq γ hγ heq
    exact C.eqOn_collarInterpolation_of_hasMFDerivAt C' h hZ hε hode hq hγ heq

end Completion
end FsFltz.Geometry
