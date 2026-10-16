import FsFltz.Geometry.RankTwoMaslov

/-!
# Joint native Maslov transport while the base coefficient varies

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 1990–2102.
This constructs the native family for the coefficient-removal edge from
one original representative. It includes genuine smooth extensions at the
parameter endpoints; it does not assert grading on the completed family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
namespace MaslovRepresentative
variable {n : ℕ} {M : SmoothManifold (2 * n)} {omega : M.Form 2}

/-- An actual native Maslov family along any smooth coefficient path whose
rank-two denominator stays nonzero on the prescribed interval. -/
def rankTwoFamily (s : MaslovRepresentative M omega)
    (homega : M.IsSmoothForm omega) (hnd : ∀ x, M.Nondegenerate omega x)
    (p q : (x : M.Point) → M.Tangent x →L[ℝ] ℝ)
    (hp : M.IsSmoothForm (covectorForm M p)) (hq : M.IsSmoothForm (covectorForm M q))
    (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k)
    (hden : ∀ t ∈ parameterInterval, ∀ x,
      1 + k t * M.rankTwoPairing omega x (hnd x) (p x) (q x) ≠ 0) :
    MaslovFamily M (fun t => M.rankTwoForm omega p q (k t)) := by
  let X := fun x => M.hamiltonianVector omega x (hnd x) (q x)
  have hX := M.isSmoothVectorField_hamiltonianVector omega homega hnd q hq
  refine
    { J := fun t x => rankTwoShearComplex (p x) (X x) (k t) (s.J x)
      tensor := fun t x => rankTwoShearTensor (p x) (X x) (k t) (s.tensor x)
      compatible := fun t ht => (s.rankTwo homega hnd p q hp hq (k t) (hden t ht)).compatible
      canonical := fun t ht x => rankTwoShearTensor_canonical (p x) (X x) (k t)
        (hden t ht x) (s.J x) (s.tensor x) (s.canonical x)
      nowhereZero := fun t ht x => rankTwoShearTensor_ne_zero (p x) (X x) (k t)
        (hden t ht x) (s.tensor x) (s.nowhereZero x)
      smoothJ := ?_
      smoothSection := ?_ }
  · intro a
    let e := chartAt (Model (2 * n)) a
    let B : Set (ℝ × Model (2 * n)) := univ ×ˢ e.target
    let pc : Model (2 * n) → Model (2 * n) →L[ℝ] ℝ :=
      fun y => (p (e.symm y)).comp (M.inverseChartTangentMap a y)
    let xc := M.vectorInChart a X
    have hpc : ContDiffOn ℝ ∞ (fun z : ℝ × Model (2 * n) => pc z.2) B :=
      (contDiffOn_covector_comp_inverseChart M p hp a).comp
        (contDiffOn_snd (s := B)) (fun _ hz => hz.2)
    have hxc : ContDiffOn ℝ ∞ (fun z : ℝ × Model (2 * n) => xc z.2) B :=
      (hX a).comp contDiffOn_snd (fun _ hz => hz.2)
    have hjc : ContDiffOn ℝ ∞ (fun z : ℝ × Model (2 * n) => almostComplexInChart M a s.J z.2) B :=
      (s.compatible.1 a).comp contDiffOn_snd (fun _ hz => hz.2)
    have hkc : ContDiffOn ℝ ∞ (fun z : ℝ × Model (2 * n) => k z.1) B :=
      hk.comp_contDiffOn contDiffOn_fst
    let D := fun z : ℝ × Model (2 * n) => 1 + k z.1 * pc z.2 (xc z.2)
    have hD : ContDiffOn ℝ ∞ D B := contDiffOn_const.add (hkc.mul (hpc.clm_apply hxc))
    let U := B ∩ D ⁻¹' {r : ℝ | r ≠ 0}
    have hU : IsOpen U := hD.continuousOn.isOpen_inter_preimage
      (isOpen_univ.prod e.open_target) isOpen_ne
    refine ⟨U, hU, ?_, ?_⟩
    · intro z hz
      refine ⟨⟨mem_univ _, hz.2⟩, ?_⟩
      change 1 + k z.1 * p (e.symm z.2)
        (M.inverseChartTangentMap a z.2 (M.vectorInChart a X z.2)) ≠ 0
      rw [M.inverseChart_vectorInChart X a hz.2]
      exact hden z.1 hz.1 _
    · exact (contDiffOn_rankTwoShearComplex (hpc.mono inter_subset_left)
        (hxc.mono inter_subset_left) (hkc.mono inter_subset_left)
        (hjc.mono inter_subset_left) (fun _ hz => hz.2)).congr
          (fun z hz => almostComplexInChart_rankTwoShearComplex M p X (k z.1) s.J a hz.1.2)
  · intro a
    let e := chartAt (Model (2 * n)) a
    let B : Set (ℝ × Model (2 * n)) := univ ×ˢ e.target
    have hpc : ContDiffOn ℝ ∞ (fun z : ℝ × Model (2 * n) =>
        ((p (e.symm z.2)).comp (M.inverseChartTangentMap a z.2) : Model (2 * n) →L[ℝ] ℝ)) B :=
      (contDiffOn_covector_comp_inverseChart M p hp a).comp
        (contDiffOn_snd (s := B)) (fun _ hz => hz.2)
    have hxc : ContDiffOn ℝ ∞ (fun z : ℝ × Model (2 * n) => M.vectorInChart a X z.2) B :=
      (hX a).comp contDiffOn_snd (fun _ hz => hz.2)
    have hsc : ContDiffOn ℝ ∞ (fun z : ℝ × Model (2 * n) =>
        squaredTensorInChart M a s.tensor z.2) B :=
      (s.smooth a).comp contDiffOn_snd (fun _ hz => hz.2)
    refine ⟨B, isOpen_univ.prod e.open_target, fun z hz => ⟨mem_univ _, hz.2⟩, ?_⟩
    exact (contDiffOn_rankTwoShearTensor hpc hxc
      (hk.comp_contDiffOn contDiffOn_fst) hsc).congr
        (fun z hz => squaredTensorInChart_rankTwoShearTensor M p X (k z.1) s.tensor a hz.2)

theorem rankTwoFamily_J_of_coefficient_zero (s : MaslovRepresentative M omega)
    (homega : M.IsSmoothForm omega) (hnd : ∀ x, M.Nondegenerate omega x)
    (p q : (x : M.Point) → M.Tangent x →L[ℝ] ℝ)
    (hp : M.IsSmoothForm (covectorForm M p)) (hq : M.IsSmoothForm (covectorForm M q))
    (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k)
    (hden : ∀ t ∈ parameterInterval, ∀ x,
      1 + k t * M.rankTwoPairing omega x (hnd x) (p x) (q x) ≠ 0)
    (t : ℝ) (ht : k t = 0) : (s.rankTwoFamily homega hnd p q hp hq k hk hden).J t = s.J := by
  funext x
  change rankTwoShearComplex (p x) _ (k t) (s.J x) = s.J x
  rw [ht, rankTwoShearComplex_zero]

theorem rankTwoFamily_tensor_of_coefficient_zero (s : MaslovRepresentative M omega)
    (homega : M.IsSmoothForm omega) (hnd : ∀ x, M.Nondegenerate omega x)
    (p q : (x : M.Point) → M.Tangent x →L[ℝ] ℝ)
    (hp : M.IsSmoothForm (covectorForm M p)) (hq : M.IsSmoothForm (covectorForm M q))
    (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k)
    (hden : ∀ t ∈ parameterInterval, ∀ x,
      1 + k t * M.rankTwoPairing omega x (hnd x) (p x) (q x) ≠ 0)
    (t : ℝ) (ht : k t = 0) :
    (s.rankTwoFamily homega hnd p q hp hq k hk hden).tensor t = s.tensor := by
  funext x
  change rankTwoShearTensor (p x) _ (k t) (s.tensor x) = s.tensor x
  rw [ht, rankTwoShearTensor_zero]

/-- Native transport along the actual primitive family. Smoothness and
nonvanishing of the section family are conclusions, not supplied data. -/
def rankTwoPrimitiveFamily {alpha : M.Form 1}
    (s : MaslovRepresentative M (M.exteriorDerivative alpha))
    (halpha : M.IsSmoothForm alpha) (hnd : ∀ x, M.Nondegenerate (M.exteriorDerivative alpha) x)
    (f : M.Point → ℂ) (hf : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f)
    (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k)
    (hden : ∀ t ∈ parameterInterval, ∀ x, 1 + k t * M.planePairing alpha f x (hnd x) ≠ 0) :
    MaslovFamily M (fun t => M.exteriorDerivative (M.rankTwoPrimitive alpha f (k t))) := by
  let F := s.rankTwoFamily (M.isSmoothForm_exteriorDerivative alpha halpha) hnd
    (fun x => Complex.reCLM.comp (complexDifferential M f x))
    (fun x => Complex.imCLM.comp (complexDifferential M f x))
    (isSmoothForm_complexDifferential_comp M hf Complex.reCLM)
    (isSmoothForm_complexDifferential_comp M hf Complex.imCLM) k hk hden
  exact
    { J := F.J
      tensor := F.tensor
      compatible := fun t ht =>
        (M.exteriorDerivative_rankTwoPrimitive_eq alpha f halpha hf (k t)).symm ▸ F.compatible t ht
      canonical := F.canonical
      nowhereZero := F.nowhereZero
      smoothJ := F.smoothJ
      smoothSection := F.smoothSection }

/-- The native grading for the actual coefficient-removal edge $K\to0$.
Nonnegative pairing supplies the denominator for the entire interval. -/
def decreasingRankTwoPrimitiveFamily {alpha : M.Form 1}
    (s : MaslovRepresentative M (M.exteriorDerivative alpha))
    (halpha : M.IsSmoothForm alpha) (hnd : ∀ x, M.Nondegenerate (M.exteriorDerivative alpha) x)
    (f : M.Point → ℂ) (hf : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f)
    (hpi : ∀ x, 0 ≤ M.planePairing alpha f x (hnd x)) (K : ℝ) (hK : 0 ≤ K) :
    MaslovFamily M (fun t => M.exteriorDerivative (M.rankTwoPrimitive alpha f (K * (1 - t)))) :=
  s.rankTwoPrimitiveFamily halpha hnd f hf (fun t => K * (1 - t))
    (contDiff_const.mul (contDiff_const.sub contDiff_id)) (fun _ ht x =>
      ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one
        (mul_nonneg (mul_nonneg hK (sub_nonneg.mpr ht.2)) (hpi x))))

end MaslovRepresentative
end FsFltz.Geometry
