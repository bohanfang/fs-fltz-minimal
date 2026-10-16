import FsFltz.Geometry.IntrinsicBoundary
import Mathlib.Analysis.ODE.ExistUnique

/-!
# One-sided uniqueness in a native half-space chart

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and
`sec:lean`, lines 783–814. The smooth-extension convention at lines
119–122 and 141 allows a Euclidean coefficient germ in a native chart.
Agreement of that germ with the intrinsic vector field is required only
at native points. No extension manifold, extended intrinsic field, or
two-sided native trajectory is supplied.

The actual manifold chain rule transports right derivatives to the chart.
Euclidean ODE uniqueness then gives native uniqueness on a common interval.
This is a local producer for gluing collar trajectories; constructing a
uniform compact collar and its completion gluing remains pending.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicCollar

/-- A smooth Euclidean coefficient germ supplies its own uniform
Lipschitz bound on a positive-radius compact convex neighborhood. -/
theorem exists_closedBall_lipschitzOnWith_of_contDiffOn {n : ℕ}
    {W : Model n → Model n} {U : Set (Model n)} {a : Model n}
    (hU : IsOpen U) (hW : ContDiffOn ℝ ∞ W U) (ha : a ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall a r ⊆ U ∧
      ∃ K : NNReal, LipschitzOnWith K W (Metric.closedBall a r) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  have hsub : Metric.closedBall a (ε / 2) ⊆ U := by
    intro x hx
    apply hball
    exact lt_of_le_of_lt hx (half_lt_self hε)
  refine ⟨ε / 2, half_pos hε, hsub, ?_⟩
  exact (hW.mono hsub).exists_lipschitzOnWith (by simp)
    (convex_closedBall a (ε / 2)) (isCompact_closedBall a (ε / 2))

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Push an actual native right ODE derivative through an atlas chart.
This uses the native chart differential also at a boundary point. -/
theorem hasDerivWithinAt_extend_of_native
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    {Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x}
    {γ : ℝ → M} {t : ℝ} (hx : γ t ∈ e.source)
    (hγ : HasMFDerivWithinAt 𝓘(ℝ, ℝ) (𝓡∂ (k + 1)) γ (Ici t) t
      (ContinuousLinearMap.toSpanSingleton ℝ (Z (γ t)))) :
    HasDerivWithinAt (fun s => e.extend (𝓡∂ (k + 1)) (γ s))
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (e.extend (𝓡∂ (k + 1))) (γ t) (Z (γ t))) (Ici t) t := by
  have he' := (e.contMDiffAt_extend (I := 𝓡∂ (k + 1))
    (IsManifold.subset_maximalAtlas (n := ∞) he) hx).mdifferentiableAt (by simp)
  have hd := hasMFDerivWithinAt_iff_hasFDerivWithinAt.mp
    (he'.hasMFDerivAt.comp_hasMFDerivWithinAt t hγ)
  apply hd.hasDerivWithinAt.congr_deriv
  change (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
    (e.extend (𝓡∂ (k + 1))) (γ t)) ((1 : ℝ) • Z (γ t)) = _
  rw [one_smul]

/-- Native right solutions of one field agree while both remain in one
chart and a common Lipschitz coefficient set. The germ is compared with
the pushed field only on that chart's native half-space points. -/
theorem eqOn_of_native_right_ode
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    {Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x}
    {W : Model (k + 1) → Model (k + 1)} {U : Set (Model (k + 1))}
    {K : NNReal} (hW : LipschitzOnWith K W U)
    (hcoeff : ∀ x ∈ e.source, e.extend (𝓡∂ (k + 1)) x ∈ U →
      W (e.extend (𝓡∂ (k + 1)) x) =
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (e.extend (𝓡∂ (k + 1))) x (Z x))
    {γ γ' : ℝ → M} {T : ℝ}
    (hγ : ContinuousOn γ (Icc 0 T)) (hγ' : ContinuousOn γ' (Icc 0 T))
    (hchart : MapsTo γ (Icc 0 T) e.source)
    (hchart' : MapsTo γ' (Icc 0 T) e.source)
    (hU : MapsTo (fun t => e.extend (𝓡∂ (k + 1)) (γ t)) (Icc 0 T) U)
    (hU' : MapsTo (fun t => e.extend (𝓡∂ (k + 1)) (γ' t)) (Icc 0 T) U)
    (hode : ∀ t ∈ Ico 0 T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) (𝓡∂ (k + 1)) γ (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ (Z (γ t))))
    (hode' : ∀ t ∈ Ico 0 T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) (𝓡∂ (k + 1)) γ' (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ (Z (γ' t))))
    (hzero : γ 0 = γ' 0) : EqOn γ γ' (Icc 0 T) := by
  have hc : ContinuousOn (fun t => e.extend (𝓡∂ (k + 1)) (γ t)) (Icc 0 T) :=
    e.continuousOn_extend.comp hγ (by simpa only [e.extend_source] using hchart)
  have hc' : ContinuousOn (fun t => e.extend (𝓡∂ (k + 1)) (γ' t)) (Icc 0 T) :=
    e.continuousOn_extend.comp hγ' (by simpa only [e.extend_source] using hchart')
  have heq := ODE_solution_unique_of_mem_Icc_right (v := fun _ => W)
    (s := fun _ => U) (fun _ _ => hW) hc
    (fun t ht => by
      rw [hcoeff _ (hchart (Ico_subset_Icc_self ht)) (hU (Ico_subset_Icc_self ht))]
      exact hasDerivWithinAt_extend_of_native he (hchart (Ico_subset_Icc_self ht))
        (hode t ht))
    (fun t ht => hU (Ico_subset_Icc_self ht)) hc'
    (fun t ht => by
      rw [hcoeff _ (hchart' (Ico_subset_Icc_self ht)) (hU' (Ico_subset_Icc_self ht))]
      exact hasDerivWithinAt_extend_of_native he (hchart' (Ico_subset_Icc_self ht))
        (hode' t ht))
    (fun t ht => hU' (Ico_subset_Icc_self ht))
    (congrArg (fun x => e.extend (𝓡∂ (k + 1)) x) hzero)
  intro t ht
  exact (e.extend (𝓡∂ (k + 1))).injOn (by simpa using hchart ht)
    (by simpa using hchart' ht) (heq ht)

/-- Smooth coefficients on a common compact convex set give native
one-sided uniqueness without a supplied Lipschitz estimate. A small
closed ball supplied by `exists_closedBall_lipschitzOnWith_of_contDiffOn`
is one such set. -/
theorem eqOn_of_native_right_ode_of_contDiffOn
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    {Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x}
    {W : Model (k + 1) → Model (k + 1)} {U : Set (Model (k + 1))}
    (hW : ContDiffOn ℝ ∞ W U) (hconv : Convex ℝ U) (hcompact : IsCompact U)
    (hcoeff : ∀ x ∈ e.source, e.extend (𝓡∂ (k + 1)) x ∈ U →
      W (e.extend (𝓡∂ (k + 1)) x) =
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (e.extend (𝓡∂ (k + 1))) x (Z x))
    {γ γ' : ℝ → M} {T : ℝ}
    (hγ : ContinuousOn γ (Icc 0 T)) (hγ' : ContinuousOn γ' (Icc 0 T))
    (hchart : MapsTo γ (Icc 0 T) e.source)
    (hchart' : MapsTo γ' (Icc 0 T) e.source)
    (hU : MapsTo (fun t => e.extend (𝓡∂ (k + 1)) (γ t)) (Icc 0 T) U)
    (hU' : MapsTo (fun t => e.extend (𝓡∂ (k + 1)) (γ' t)) (Icc 0 T) U)
    (hode : ∀ t ∈ Ico 0 T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) (𝓡∂ (k + 1)) γ (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ (Z (γ t))))
    (hode' : ∀ t ∈ Ico 0 T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) (𝓡∂ (k + 1)) γ' (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ (Z (γ' t))))
    (hzero : γ 0 = γ' 0) : EqOn γ γ' (Icc 0 T) := by
  obtain ⟨K, hK⟩ := hW.exists_lipschitzOnWith (by simp) hconv hcompact
  exact eqOn_of_native_right_ode he hK hcoeff hγ hγ' hchart hchart' hU hU'
    hode hode' hzero


/-- Two native right solutions with the same starting point agree on a
positive common time interval. Smooth local coefficients supply a compact
Lipschitz ball, and continuity supplies the common chart and coefficient
containment; these trajectory bounds are conclusions of the proof. -/
theorem exists_pos_eqOn_of_native_right_ode
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    {Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x}
    {W : Model (k + 1) → Model (k + 1)} {U : Set (Model (k + 1))}
    (hU : IsOpen U) (hW : ContDiffOn ℝ ∞ W U)
    (hcoeff : ∀ x ∈ e.source, e.extend (𝓡∂ (k + 1)) x ∈ U →
      W (e.extend (𝓡∂ (k + 1)) x) =
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (e.extend (𝓡∂ (k + 1))) x (Z x))
    {γ γ' : ℝ → M} {T : ℝ} (hT : 0 < T)
    (hγ : ContinuousOn γ (Icc 0 T)) (hγ' : ContinuousOn γ' (Icc 0 T))
    (hode : ∀ t ∈ Ico 0 T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) (𝓡∂ (k + 1)) γ (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ (Z (γ t))))
    (hode' : ∀ t ∈ Ico 0 T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) (𝓡∂ (k + 1)) γ' (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ (Z (γ' t))))
    (hsource : γ 0 ∈ e.source)
    (hcoord : e.extend (𝓡∂ (k + 1)) (γ 0) ∈ U)
    (hzero : γ 0 = γ' 0) : ∃ ε : ℝ, 0 < ε ∧ ε < T ∧ EqOn γ γ' (Icc 0 ε) := by
  let a := e.extend (𝓡∂ (k + 1)) (γ 0)
  obtain ⟨r, hr, hsub, K, hK⟩ :=
    exists_closedBall_lipschitzOnWith_of_contDiffOn hU hW hcoord
  let N : Set M := e.source ∩ (e.extend (𝓡∂ (k + 1))) ⁻¹' Metric.closedBall a r
  have hec := (e.contMDiffAt_extend (I := 𝓡∂ (k + 1))
    (IsManifold.subset_maximalAtlas (n := ∞) he) hsource).continuousAt
  have hN : N ∈ 𝓝 (γ 0) :=
    inter_mem (e.open_source.mem_nhds hsource)
      (hec.preimage_mem_nhds (Metric.closedBall_mem_nhds a hr))
  have hN' : N ∈ 𝓝 (γ' 0) := by rw [← hzero]; exact hN
  have hz : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, le_of_lt hT⟩
  have hboth : γ ⁻¹' N ∩ γ' ⁻¹' N ∈ 𝓝[Icc 0 T] (0 : ℝ) :=
    inter_mem ((hγ 0 hz).preimage_mem_nhdsWithin hN)
      ((hγ' 0 hz).preimage_mem_nhdsWithin hN')
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hboth
  let ε : ℝ := min δ T / 2
  have hε : 0 < ε := half_pos (lt_min hδ hT)
  have hεδ : ε < δ := lt_of_lt_of_le (half_lt_self (lt_min hδ hT)) (min_le_left _ _)
  have hεT : ε < T := lt_of_lt_of_le (half_lt_self (lt_min hδ hT)) (min_le_right _ _)
  have hinterval : Icc (0 : ℝ) ε ⊆ Icc 0 T :=
    Icc_subset_Icc_right (le_of_lt hεT)
  have hmem : ∀ t ∈ Icc (0 : ℝ) ε, γ t ∈ N ∧ γ' t ∈ N := by
    intro t ht
    apply hδsub
    refine ⟨?_, hinterval ht⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact lt_of_le_of_lt ht.2 hεδ
  refine ⟨ε, hε, hεT, ?_⟩
  apply eqOn_of_native_right_ode he hK
    (fun x hx hy => hcoeff x hx (hsub hy))
    (hγ.mono hinterval) (hγ'.mono hinterval)
    (fun t ht => (hmem t ht).1.1) (fun t ht => (hmem t ht).2.1)
    (fun t ht => (hmem t ht).1.2) (fun t ht => (hmem t ht).2.2)
    (fun t ht => hode t ⟨ht.1, lt_trans ht.2 hεT⟩)
    (fun t ht => hode' t ⟨ht.1, lt_trans ht.2 hεT⟩) hzero


end FsFltz.Geometry.IntrinsicCollar
