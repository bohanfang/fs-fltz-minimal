import FsFltz.Geometry.RankTwoMaslovFamily

/-!
# Joint Maslov transport for varying rank-two covectors

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 1994–2030.
The actual Hamiltonian vector of a smoothly varying covector is jointly
smooth. The explicit shear then gives a native Maslov family, with real
open extensions at both endpoints. The nonzero-denominator locus supplies
the required open neighborhood without a uniform time margin.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
namespace SmoothManifold

theorem IsSmoothFormFamily.slice {d r : ℕ} {M : SmoothManifold d}
    {α : ℝ → M.Form r} (hα : M.IsSmoothFormFamily α)
    {t : ℝ} (ht : t ∈ parameterInterval) : M.IsSmoothForm (α t) := by
  intro a y hy
  obtain ⟨U, hU, hcover, hcoeff⟩ := hα a
  exact ((hcoeff.contDiffAt (hU.mem_nhds (hcover ⟨ht, hy⟩))).comp y
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

/-- Joint inverse-chart covector coefficients follow from the native form
family contract, through the one-form linear isometry. -/
theorem smoothNearInterval_covector_comp_inverseChart {d : ℕ} (M : SmoothManifold d)
    (q : ℝ → (x : M.Point) → M.Tangent x →L[ℝ] ℝ)
    (hq : M.IsSmoothFormFamily (fun t => covectorForm M (q t))) (a : M.Point) :
    SmoothNearInterval (chartAt (Model d) a).target
      (fun z : ℝ × Model d => ((q z.1 ((chartAt (Model d) a).symm z.2)).comp
        (M.inverseChartTangentMap a z.2) : Model d →L[ℝ] ℝ)) := by
  obtain ⟨U, hU, hcover, hs⟩ := hq a
  let e := (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model d) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv
  refine ⟨U, hU, hcover, ?_⟩
  apply (e.symm.contDiff.comp_contDiffOn hs).congr
  intro z _
  apply e.injective
  ext v
  rfl

/-- Hamiltonian inversion preserves genuine joint regularity of a varying
covector family for a fixed smooth symplectic form. -/
theorem isSmoothVectorFieldFamily_hamiltonianVector {d : ℕ} (M : SmoothManifold d)
    (omega : M.Form 2) (homega : M.IsSmoothForm omega) (hnd : ∀ x, M.Nondegenerate omega x)
    (q : ℝ → (x : M.Point) → M.Tangent x →L[ℝ] ℝ)
    (hq : M.IsSmoothFormFamily (fun t => covectorForm M (q t))) :
    M.IsSmoothVectorFieldFamily (fun t x => M.hamiltonianVector omega x (hnd x) (q t x)) := by
  intro a
  let e := chartAt (Model d) a
  obtain ⟨U, hU, hcover, hs⟩ := hq a
  let V := U ∩ (univ ×ˢ e.target)
  let A : Model d → Model d →L[ℝ] Model d :=
    fun y => chartContraction (M.formInChart a omega y)
  have hcur : ContDiff ℝ ∞ (ContinuousAlternatingMap.curryLeft :
      (Model d [⋀^Fin 2]→L[ℝ] ℝ) → Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Model d [⋀^Fin 2]→L[ℝ] ℝ)
      (F := Model d →L[ℝ] Model d [⋀^Fin 1]→L[ℝ] ℝ)
      (ContinuousAlternatingMap.curryLeftLI
        (𝕜 := ℝ) (E := Model d) (F := ℝ) (n := 1)).toContinuousLinearMap
  have hA : ContDiffOn ℝ ∞ A e.target :=
    contDiffOn_const.clm_comp (hcur.comp_contDiffOn (homega a))
  have hinv (y) (hy : y ∈ e.target) : (A y).IsInvertible :=
    chartContraction_invertible _ (M.nondegenerate_formInChart omega a hy (hnd _))
  have hAi : ContDiffOn ℝ ∞ (fun y => (A y).inverse) e.target := by
    intro y hy
    exact (hinv y hy).contDiffAt_map_inverse.comp_contDiffWithinAt y (hA y hy)
  have hAv : ContDiffOn ℝ ∞ (fun z : ℝ × Model d => (A z.2).inverse) V :=
    hAi.comp contDiffOn_snd (fun _ hz => hz.2.2)
  have hb := (chartOneFormEquiv d).symm.contDiff.comp_contDiffOn
    (hs.mono (show V ⊆ U from inter_subset_left))
  refine ⟨V, hU.inter (isOpen_univ.prod e.open_target),
    fun z hz => ⟨hcover hz, ⟨mem_univ _, hz.2⟩⟩, ?_⟩
  apply (hAv.clm_apply hb).congr
  intro z hz
  symm
  apply (hinv z.2 hz.2.2).inverse_apply_eq.mpr
  exact congrArg (chartOneFormEquiv d).symm
    (M.hamiltonianVector_chart_contraction omega hnd (q z.1) a hz.2.2).symm

end SmoothManifold

/-- Affine complex maps have jointly smooth real covector differentials. -/
theorem isSmoothFormFamily_complexDifferential_affine {d : ℕ} (M : SmoothManifold d)
    {f g : M.Point → ℂ}
    (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ g) (L : ℂ →L[ℝ] ℝ) :
    M.IsSmoothFormFamily (fun t => covectorForm M
      (fun x => L.comp (complexDifferential M (f + t • g) x))) := by
  have hd (t : ℝ) (x : M.Point) : complexDifferential M (f + t • g) x =
      complexDifferential M f x + t • complexDifferential M g x :=
    ((hf.mdifferentiable (by simp) x).hasMFDerivAt.add
      ((hg.mdifferentiable (by simp) x).hasMFDerivAt.const_smul t)).mfderiv
  have he (t : ℝ) : covectorForm M (fun x => L.comp (complexDifferential M (f + t • g) x)) =
      covectorForm M (fun x => L.comp (complexDifferential M f x)) +
        t • covectorForm M (fun x => L.comp (complexDifferential M g x)) := by
    funext x
    ext v
    simp [covectorForm, hd]
  intro a
  let e := chartAt (Model d) a
  let B : Set (ℝ × Model d) := univ ×ˢ e.target
  have h0 := (isSmoothForm_complexDifferential_comp M hf L a).comp
    (contDiffOn_snd (s := B)) (fun _ hz => hz.2)
  have h1 := (isSmoothForm_complexDifferential_comp M hg L a).comp
    (contDiffOn_snd (s := B)) (fun _ hz => hz.2)
  refine ⟨B, isOpen_univ.prod e.open_target, fun z hz => ⟨mem_univ _, hz.2⟩, ?_⟩
  apply (h0.add (contDiffOn_fst.smul h1)).congr
  intro z _
  dsimp only
  rw [he z.1, M.formInChart_add, M.formInChart_smul]
  rfl

namespace MaslovRepresentative
variable {n : ℕ} {M : SmoothManifold (2 * n)} {omega : M.Form 2}

/-- Varying covectors and a smooth coefficient path construct an actual
native Maslov family for the corresponding rank-two forms. -/
def rankTwoVaryingFamily (s : MaslovRepresentative M omega)
    (homega : M.IsSmoothForm omega) (hnd : ∀ x, M.Nondegenerate omega x)
    (p q : ℝ → (x : M.Point) → M.Tangent x →L[ℝ] ℝ)
    (hp : M.IsSmoothFormFamily (fun t => covectorForm M (p t)))
    (hq : M.IsSmoothFormFamily (fun t => covectorForm M (q t)))
    (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k)
    (hden : ∀ t ∈ parameterInterval, ∀ x,
      1 + k t * M.rankTwoPairing omega x (hnd x) (p t x) (q t x) ≠ 0) :
    MaslovFamily M (fun t => M.rankTwoForm omega (p t) (q t) (k t)) := by
  let X := fun t x => M.hamiltonianVector omega x (hnd x) (q t x)
  have hX := M.isSmoothVectorFieldFamily_hamiltonianVector omega homega hnd q hq
  refine
    { J := fun t x => rankTwoShearComplex (p t x) (X t x) (k t) (s.J x)
      tensor := fun t x => rankTwoShearTensor (p t x) (X t x) (k t) (s.tensor x)
      compatible := fun t ht =>
        (s.rankTwo homega hnd (p t) (q t) (hp.slice ht) (hq.slice ht) (k t) (hden t ht)).compatible
      canonical := fun t ht x => rankTwoShearTensor_canonical (p t x) (X t x) (k t)
        (hden t ht x) (s.J x) (s.tensor x) (s.canonical x)
      nowhereZero := fun t ht x => rankTwoShearTensor_ne_zero (p t x) (X t x) (k t)
        (hden t ht x) (s.tensor x) (s.nowhereZero x)
      smoothJ := ?_
      smoothSection := ?_ }
  · intro a
    let e := chartAt (Model (2 * n)) a
    obtain ⟨P, hP, hPi, hpc⟩ := M.smoothNearInterval_covector_comp_inverseChart p hp a
    obtain ⟨V, hV, hVi, hxc⟩ := hX a
    let B := (P ∩ V) ∩ (univ ×ˢ e.target)
    have hB : IsOpen B := (hP.inter hV).inter (isOpen_univ.prod e.open_target)
    let pc : ℝ × Model (2 * n) → Model (2 * n) →L[ℝ] ℝ := fun z =>
      (p z.1 (e.symm z.2)).comp (M.inverseChartTangentMap a z.2)
    let xc := fun z : ℝ × Model (2 * n) => M.vectorInChart a (X z.1) z.2
    have hpB : ContDiffOn ℝ ∞ pc B := hpc.mono (fun _ hz => hz.1.1)
    have hxB : ContDiffOn ℝ ∞ xc B := hxc.mono (fun _ hz => hz.1.2)
    have hjB : ContDiffOn ℝ ∞
        (fun z : ℝ × Model (2 * n) => almostComplexInChart M a s.J z.2) B :=
      (s.compatible.1 a).comp contDiffOn_snd (fun _ hz => hz.2.2)
    have hkB : ContDiffOn ℝ ∞ (fun z : ℝ × Model (2 * n) => k z.1) B :=
      hk.comp_contDiffOn contDiffOn_fst
    let D := fun z : ℝ × Model (2 * n) => 1 + k z.1 * pc z (xc z)
    have hD : ContDiffOn ℝ ∞ D B := contDiffOn_const.add (hkB.mul (hpB.clm_apply hxB))
    let U := B ∩ D ⁻¹' {r : ℝ | r ≠ 0}
    refine ⟨U, hD.continuousOn.isOpen_inter_preimage hB isOpen_ne, ?_, ?_⟩
    · intro z hz
      refine ⟨⟨⟨hPi hz, hVi hz⟩, ⟨mem_univ _, hz.2⟩⟩, ?_⟩
      change 1 + k z.1 * p z.1 (e.symm z.2)
        (M.inverseChartTangentMap a z.2 (M.vectorInChart a (X z.1) z.2)) ≠ 0
      rw [M.inverseChart_vectorInChart (X z.1) a hz.2]
      exact hden z.1 hz.1 _
    · exact (contDiffOn_rankTwoShearComplex (hpB.mono inter_subset_left)
        (hxB.mono inter_subset_left) (hkB.mono inter_subset_left)
        (hjB.mono inter_subset_left) (fun _ hz => hz.2)).congr
          (fun z hz => almostComplexInChart_rankTwoShearComplex M (p z.1) (X z.1)
            (k z.1) s.J a hz.1.2.2)
  · intro a
    let e := chartAt (Model (2 * n)) a
    obtain ⟨P, hP, hPi, hpc⟩ := M.smoothNearInterval_covector_comp_inverseChart p hp a
    obtain ⟨V, hV, hVi, hxc⟩ := hX a
    let B := (P ∩ V) ∩ (univ ×ˢ e.target)
    have hsc : ContDiffOn ℝ ∞
        (fun z : ℝ × Model (2 * n) => squaredTensorInChart M a s.tensor z.2) B :=
      (s.smooth a).comp contDiffOn_snd (fun _ hz => hz.2.2)
    refine ⟨B, (hP.inter hV).inter (isOpen_univ.prod e.open_target),
      fun z hz => ⟨⟨hPi hz, hVi hz⟩, ⟨mem_univ _, hz.2⟩⟩, ?_⟩
    exact (contDiffOn_rankTwoShearTensor (hpc.mono (fun _ hz => hz.1.1))
      (hxc.mono (fun _ hz => hz.1.2))
      (hk.comp_contDiffOn contDiffOn_fst) hsc).congr
        (fun z hz => squaredTensorInChart_rankTwoShearTensor M (p z.1) (X z.1)
          (k z.1) s.tensor a hz.2.2)

/-- Joint differential data for varying complex maps give a native family
for their actual primitive updates. -/
def rankTwoPrimitiveVaryingFamily {α : M.Form 1}
    (s : MaslovRepresentative M (M.exteriorDerivative α))
    (hα : M.IsSmoothForm α) (hnd : ∀ x, M.Nondegenerate (M.exteriorDerivative α) x)
    (f : ℝ → M.Point → ℂ)
    (hf : ∀ t ∈ parameterInterval, ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞ (f t))
    (hp : M.IsSmoothFormFamily (fun t => covectorForm M
      (fun x => Complex.reCLM.comp (complexDifferential M (f t) x))))
    (hq : M.IsSmoothFormFamily (fun t => covectorForm M
      (fun x => Complex.imCLM.comp (complexDifferential M (f t) x))))
    (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k)
    (hden : ∀ t ∈ parameterInterval, ∀ x, 1 + k t * M.planePairing α (f t) x (hnd x) ≠ 0) :
    MaslovFamily M (fun t => M.exteriorDerivative (M.rankTwoPrimitive α (f t) (k t))) := by
  let F := s.rankTwoVaryingFamily (M.isSmoothForm_exteriorDerivative α hα) hnd
    (fun t x => Complex.reCLM.comp (complexDifferential M (f t) x))
    (fun t x => Complex.imCLM.comp (complexDifferential M (f t) x)) hp hq k hk hden
  exact { J := F.J, tensor := F.tensor
          compatible := fun t ht => by
            rw [M.exteriorDerivative_rankTwoPrimitive_eq α (f t) hα (hf t ht) (k t)]
            exact F.compatible t ht
          canonical := F.canonical, nowhereZero := F.nowhereZero
          smoothJ := F.smoothJ, smoothSection := F.smoothSection }

end MaslovRepresentative
end FsFltz.Geometry
