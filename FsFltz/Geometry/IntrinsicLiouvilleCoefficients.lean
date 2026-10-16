import FsFltz.Geometry.IntrinsicLiouvilleExtension

/-!
# Local smooth coefficients of the intrinsic Liouville field

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and
`sec:lean`, lines 783–814. Smooth primitive extension germs and the actual
exterior-derivative equation produce smooth coefficient germs of the unique
contraction field. No vector-field extension or global extension manifold
is assumed. Existence of the exterior-derivative equation is a separate bridge.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The intrinsic algebraic contraction solution; nondegeneracy proves its
defining equation. Its definition does not choose a flow or any extension. -/
def liouvilleVector (α : Form k M 1) (omega : Form k M 2) (x : M) :
    TangentSpace (𝓡∂ (k + 1)) x :=
  (SmoothManifold.chartContraction (omega x)).inverse
    ((SmoothManifold.chartOneFormEquiv (k + 1)).symm (α x))

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem contraction_liouvilleVector (α : Form k M 1) (omega : Form k M 2)
    (hnd : ∀ x, Nondegenerate omega x) : Contraction α omega (liouvilleVector α omega) := by
  intro x v
  let o : Model (k + 1) [⋀^Fin 2]→L[ℝ] ℝ := omega x
  let a : Model (k + 1) [⋀^Fin 1]→L[ℝ] ℝ := α x
  have hi := SmoothManifold.chartContraction_invertible o (hnd x)
  have he : o.curryLeft (liouvilleVector α omega x) = a := by
    apply (SmoothManifold.chartOneFormEquiv (k + 1)).symm.injective
    exact hi.self_apply_inverse _
  have hv := congrArg (fun β => β ![v]) he
  convert hv using 1
  apply congrArg (omega x)
  funext i
  fin_cases i <;> rfl

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem contraction_unique (α : Form k M 1) (omega : Form k M 2)
    (hnd : ∀ x, Nondegenerate omega x)
    {Z Z' : (x : M) → TangentSpace (𝓡∂ (k + 1)) x}
    (hZ : Contraction α omega Z) (hZ' : Contraction α omega Z') : Z = Z' := by
  funext x
  apply sub_eq_zero.mp
  apply hnd x
  intro v
  rw [(omega x).map_vecCons_sub, hZ x v, hZ' x v, sub_self]

/-- The same locally extendible primitive constructs smooth vector coefficients
of any field satisfying its nondegenerate contraction equation. The extension
of the two-form and the field are both derived, not supplied. -/
theorem exists_liouville_coefficients
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    (α : Form k M 1) (omega : Form k M 2) (hα : IsLocallyExtendibleForm α)
    (hd : HasExteriorDerivative α omega) (hnd : ∀ x, Nondegenerate omega x)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x) (hZ : Contraction α omega Z)
    {x : M} (hx : x ∈ e.source) :
    ∃ (f : Model (k + 1) → Model (k + 1)) (V : Set (Model (k + 1))),
      IsOpen V ∧ e.extend (𝓡∂ (k + 1)) x ∈ V ∧ ContDiffOn ℝ ∞ f V ∧
      f =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target]
        (e.extend (𝓡∂ (k + 1)) x)] vectorInChart e Z := by
  obtain ⟨β, U, hU, haU, hβ, hag⟩ := hα e he x hx
  obtain ⟨hD, hDag⟩ := exists_exteriorDerivative_extension he hd hU haU hβ hag
  let A : Model (k + 1) → Model (k + 1) →L[ℝ] Model (k + 1) :=
    fun y => SmoothManifold.chartContraction (extDeriv β y)
  let b : Model (k + 1) → Model (k + 1) :=
    fun y => (SmoothManifold.chartOneFormEquiv (k + 1)).symm (β y)
  have hcur : ContDiff ℝ ∞ (ContinuousAlternatingMap.curryLeft :
      (Model (k + 1) [⋀^Fin 2]→L[ℝ] ℝ) →
        Model (k + 1) →L[ℝ] Model (k + 1) [⋀^Fin 1]→L[ℝ] ℝ) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Model (k + 1) [⋀^Fin 2]→L[ℝ] ℝ)
      (F := Model (k + 1) →L[ℝ] Model (k + 1) [⋀^Fin 1]→L[ℝ] ℝ)
      (ContinuousAlternatingMap.curryLeftLI
        (𝕜 := ℝ) (E := Model (k + 1)) (F := ℝ) (n := 1)).toContinuousLinearMap
  have hA : ContDiffOn ℝ ∞ A U :=
    contDiffOn_const.clm_comp (hcur.comp_contDiffOn hD)
  have hb : ContDiffOn ℝ ∞ b U :=
    (SmoothManifold.chartOneFormEquiv (k + 1)).symm.contDiff.comp_contDiffOn hβ
  have hat : e.extend (𝓡∂ (k + 1)) x ∈ (e.extend (𝓡∂ (k + 1))).target :=
    (e.extend (𝓡∂ (k + 1))).map_source (by simpa only [e.extend_source] using hx)
  have hAa : (A (e.extend (𝓡∂ (k + 1)) x)).IsInvertible := by
    dsimp only [A]
    rw [hDag.eq_of_nhdsWithin hat]
    apply SmoothManifold.chartContraction_invertible
    apply nondegenerate_formInChart he omega hat
    exact hnd _
  let V : Set (Model (k + 1)) := U ∩ {y | (A y).IsInvertible}
  have hV : IsOpen V :=
    hA.continuousOn.isOpen_inter_preimage hU ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have haV : e.extend (𝓡∂ (k + 1)) x ∈ V := ⟨haU, hAa⟩
  have hAi : ContDiffOn ℝ ∞ (fun y => (A y).inverse) V := by
    intro y hy
    exact hy.2.contDiffAt_map_inverse.comp_contDiffWithinAt y (hA y hy.1 |>.mono inter_subset_left)
  let f : Model (k + 1) → Model (k + 1) := fun y => (A y).inverse (b y)
  refine ⟨f, V, hV, haV, hAi.clm_apply (hb.mono inter_subset_left), ?_⟩
  filter_upwards [hag, hDag, self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (hV.mem_nhds haV)] with y hy hDy hyt hyV
  change (A y).inverse (b y) = vectorInChart e Z y
  apply hyV.2.inverse_apply_eq.mpr
  dsimp only [b, A, SmoothManifold.chartContraction]
  rw [hy, hDy]
  change (SmoothManifold.chartOneFormEquiv (k + 1)).symm (formInChart e α y) =
    (SmoothManifold.chartOneFormEquiv (k + 1)).symm
      ((formInChart e omega y).curryLeft (vectorInChart e Z y))
  rw [contraction_inChart he α omega Z hZ hyt]

/-- The inward field of the form-determined Liouville vector has precisely
the scalar smooth extension germs consumed by native collar construction. -/
theorem inward_liouvilleVector_scalar_extensions
    (α : Form k M 1) (omega : Form k M 2) (hα : IsLocallyExtendibleForm α)
    (hd : HasExteriorDerivative α omega) (hnd : ∀ x, Nondegenerate omega x)
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)))
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) (x : M) (hx : x ∈ e.source)
    (i : Fin (k + 1)) :
    ∃ (f : Model (k + 1) → ℝ) (V : Set (Model (k + 1))),
      IsOpen V ∧ e.extend (𝓡∂ (k + 1)) x ∈ V ∧ ContDiffOn ℝ ∞ f V ∧
      f =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target]
        (e.extend (𝓡∂ (k + 1)) x)]
        (fun y => vectorInChart e (fun x => -liouvilleVector α omega x) y i) := by
  obtain ⟨F, V, hV, hxV, hF, heq⟩ := exists_liouville_coefficients he α omega hα hd hnd
    (liouvilleVector α omega) (contraction_liouvilleVector α omega hnd) hx
  refine ⟨fun y => -(F y i), V, hV, hxV, ?_, ?_⟩
  · exact ((EuclideanSpace.proj i).contDiff.comp_contDiffOn hF).neg
  · filter_upwards [heq] with y hy
    have hn : vectorInChart e (fun x => -liouvilleVector α omega x) y =
        -vectorInChart e (liouvilleVector α omega) y := by
      unfold vectorInChart
      rw [map_neg]
    rw [hn, ← hy]
    rfl

end FsFltz.Geometry.IntrinsicLiouville
