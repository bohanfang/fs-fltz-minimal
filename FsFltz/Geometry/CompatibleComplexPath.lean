import FsFltz.Geometry.CompatibleComplexTransport

/-!
# Constructing paths of compatible complex structures

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244;
`thm:target` / `g:chain`, lines 407–413; `sec:lean`, lines 794–814.

Let `J₀,J₁` be compatible with the same two-form. Put
`a=1-t/2`, `b=t/2`, and `Tₜ=a id-b J₁J₀`. Compatibility gives
`ω(TₜJ₀u,TₜJ₀v)=ω(Tₜu,Tₜv)` and
`ω(Tₜu,TₜJ₀u)=(a²+b²)ω(u,J₀u)+ab(ω(u,J₁u)+ω(J₀u,J₁J₀u))`.
On `[0,1]`, `a>0` and `b≥0`, so the latter expression is positive
for every nonzero `u`. Therefore `Tₜ` is injective and hence invertible.
Conjugation by `Tₜ` then produces a compatible structure from `J₀`.
At zero `Tₜ=id`; at one it is the normalized intertwiner from `J₀`
to `J₁`. These formulas do not require positive dimension.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry

/-- The polynomial interpolation between the identity and the normalized
intertwiner from the initial structure to the terminal structure. -/
def compatibleComplexPathMap {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (J₀ J₁ : E →L[ℝ] E) (t : ℝ) : E →L[ℝ] E :=
  (1 - t / 2) • ContinuousLinearMap.id ℝ E - (t / 2) • J₁.comp J₀

@[simp] theorem compatibleComplexPathMap_zero {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (J₀ J₁ : E →L[ℝ] E) :
    compatibleComplexPathMap J₀ J₁ 0 = ContinuousLinearMap.id ℝ E := by
  simp [compatibleComplexPathMap]

@[simp] theorem compatibleComplexPathMap_one {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (J₀ J₁ : E →L[ℝ] E) :
    compatibleComplexPathMap J₀ J₁ 1 = compatibleComplexTransport J₁ J₀ := by
  ext v
  simp only [compatibleComplexPathMap, compatibleComplexTransport, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    smul_sub]
  norm_num

theorem compatibleComplexPathMap_apply_J {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (J₀ J₁ : E →L[ℝ] E)
    (h₀ : ∀ v, J₀ (J₀ v) = -v) (t : ℝ) (v : E) :
    compatibleComplexPathMap J₀ J₁ t (J₀ v) =
      (1 - t / 2) • J₀ v + (t / 2) • J₁ v := by
  simp [compatibleComplexPathMap, h₀, sub_neg_eq_add]

namespace SmoothManifold

theorem evalTwo_add_right {d : ℕ} {M : SmoothManifold d} (eta : M.Form 2)
    (x : M.Point) (u v w : M.Tangent x) :
    evalTwo eta x u (v + w) = evalTwo eta x u v + evalTwo eta x u w := by
  rw [evalTwo_swap eta x u (v + w), evalTwo_add_left,
    evalTwo_swap eta x v u, evalTwo_swap eta x w u]
  ring

end SmoothManifold

theorem compatibleAlmostComplex_skew {d : ℕ} {M : SmoothManifold d}
    {eta : M.Form 2} {J : AlmostComplexField M}
    (hJ : IsCompatibleAlmostComplex M eta J) (x : M.Point)
    (u v : M.Tangent x) :
    SmoothManifold.evalTwo eta x (J x u) v =
      -SmoothManifold.evalTwo eta x u (J x v) := by
  have hh := hJ.2.2.1 x u (-J x v)
  have hn : SmoothManifold.evalTwo eta x u (-J x v) =
      -SmoothManifold.evalTwo eta x u (J x v) := by
    simpa only [neg_one_smul, neg_one_mul] using
      SmoothManifold.evalTwo_smul_right eta x (-1) u (J x v)
  simpa only [map_neg, hJ.2.1, neg_neg, hn] using hh

set_option backward.isDefEq.respectTransparency false in
/-- The interpolating map pulls the two-form back to a form invariant
under the initial complex structure. -/
theorem compatibleComplexPathMap_preserves_J_form {d : ℕ}
    (M : SmoothManifold d) (eta : M.Form 2) (J₀ J₁ : AlmostComplexField M)
    (h₀ : IsCompatibleAlmostComplex M eta J₀)
    (h₁ : IsCompatibleAlmostComplex M eta J₁) (t : ℝ) (x : M.Point)
    (u v : M.Tangent x) :
    SmoothManifold.evalTwo eta x
      (compatibleComplexPathMap (J₀ x) (J₁ x) t (J₀ x u))
      (compatibleComplexPathMap (J₀ x) (J₁ x) t (J₀ x v)) =
    SmoothManifold.evalTwo eta x
      (compatibleComplexPathMap (J₀ x) (J₁ x) t u)
      (compatibleComplexPathMap (J₀ x) (J₁ x) t v) := by
  rw [compatibleComplexPathMap_apply_J _ _ (h₀.2.1 x),
    compatibleComplexPathMap_apply_J _ _ (h₀.2.1 x)]
  simp only [compatibleComplexPathMap, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    SmoothManifold.evalTwo_add_left, SmoothManifold.evalTwo_add_right,
    SmoothManifold.evalTwo_sub_left, SmoothManifold.evalTwo_sub_right,
    SmoothManifold.evalTwo_smul_left, SmoothManifold.evalTwo_smul_right,
    h₀.2.2.1, h₁.2.2.1]
  have hs₀ := compatibleAlmostComplex_skew h₁ x (J₀ x u) v
  have hs₁ := compatibleAlmostComplex_skew h₁ x u (J₀ x v)
  rw [hs₀, hs₁]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The positive quadratic identity gives invertibility throughout the
whole closed interval, without any closeness assumption. -/
theorem compatibleComplexPathMap_positive {d : ℕ}
    (M : SmoothManifold d) (eta : M.Form 2) (J₀ J₁ : AlmostComplexField M)
    (h₀ : IsCompatibleAlmostComplex M eta J₀)
    (h₁ : IsCompatibleAlmostComplex M eta J₁) (t : ℝ) (ht : t ∈ parameterInterval)
    (x : M.Point) (u : M.Tangent x) (hu : u ≠ 0) :
    0 < SmoothManifold.evalTwo eta x
      (compatibleComplexPathMap (J₀ x) (J₁ x) t u)
      (compatibleComplexPathMap (J₀ x) (J₁ x) t (J₀ x u)) := by
  have huJ : J₀ x u ≠ 0 := by
    intro hz
    have hh := h₀.2.1 x u
    rw [hz, map_zero] at hh
    exact hu (neg_eq_zero.mp hh.symm)
  have hp₀ := h₀.2.2.2 x u hu
  have hp₁ := h₁.2.2.2 x u hu
  have hp₂ := h₁.2.2.2 x (J₀ x u) huJ
  have hs₀ := compatibleAlmostComplex_skew h₁ x (J₀ x u) (J₀ x u)
  have hs₁ := h₁.2.2.1 x (J₀ x u) u
  have hs₂ := compatibleAlmostComplex_skew h₀ x u u
  rw [compatibleComplexPathMap_apply_J _ _ (h₀.2.1 x)]
  simp only [compatibleComplexPathMap, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    SmoothManifold.evalTwo_add_right, SmoothManifold.evalTwo_sub_left,
    SmoothManifold.evalTwo_smul_left, SmoothManifold.evalTwo_smul_right]
  rw [hs₀, hs₁, hs₂]
  have ha : 0 < 1 - t / 2 := by linarith [ht.2]
  have hb : 0 ≤ t / 2 := by linarith [ht.1]
  have hmain : 0 < (1 - t / 2) ^ 2 * SmoothManifold.evalTwo eta x u (J₀ x u) :=
    mul_pos (sq_pos_of_pos ha) hp₀
  have hrest : 0 ≤ (t / 2) ^ 2 * SmoothManifold.evalTwo eta x u (J₀ x u) :=
    mul_nonneg (sq_nonneg _) hp₀.le
  have hc₁ : 0 ≤ (1 - t / 2) * (t / 2) *
      SmoothManifold.evalTwo eta x u (J₁ x u) :=
    mul_nonneg (mul_nonneg ha.le hb) hp₁.le
  have hc₂ : 0 ≤ (1 - t / 2) * (t / 2) *
      SmoothManifold.evalTwo eta x (J₀ x u) (J₁ x (J₀ x u)) :=
    mul_nonneg (mul_nonneg ha.le hb) hp₂.le
  nlinarith

set_option backward.isDefEq.respectTransparency false in
theorem compatibleComplexPathMap_isInvertible {d : ℕ}
    (M : SmoothManifold d) (eta : M.Form 2) (J₀ J₁ : AlmostComplexField M)
    (h₀ : IsCompatibleAlmostComplex M eta J₀)
    (h₁ : IsCompatibleAlmostComplex M eta J₁) (t : ℝ) (ht : t ∈ parameterInterval)
    (x : M.Point) :
    (compatibleComplexPathMap (J₀ x) (J₁ x) t).IsInvertible := by
  let A := compatibleComplexPathMap (E := Model d) (J₀ x) (J₁ x) t
  have hker : A.toLinearMap.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    change A u = 0 at hu
    by_contra hne
    have hp := compatibleComplexPathMap_positive M eta J₀ J₁ h₀ h₁ t ht x u hne
    change 0 < SmoothManifold.evalTwo eta x (A u) (A (J₀ x u)) at hp
    rw [hu] at hp
    have hz : SmoothManifold.evalTwo eta x 0 (A (J₀ x u)) = 0 := by
      simpa using SmoothManifold.evalTwo_smul_left eta x 0 u (A (J₀ x u))
    rw [hz] at hp
    exact lt_irrefl 0 hp
  have hinj : Function.Injective A := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective A := LinearMap.injective_iff_surjective.mp hinj
  change A.IsInvertible
  exact ⟨ContinuousLinearEquiv.ofBijective A hker
    (LinearMap.range_eq_top.mpr hsurj), ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- Conjugating by the interpolating map. Its total inverse is used only
on its proved open invertibility locus in smoothness statements. -/
def compatibleComplexPathStructure {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (J₀ J₁ : E →L[ℝ] E) (t : ℝ) : E →L[ℝ] E :=
  let A := compatibleComplexPathMap J₀ J₁ t
  A.comp (J₀.comp A.inverse)

/-- The prescribed explicit path on the actual ambient tangent fibers. -/
def compatibleComplexPath {d : ℕ} (M : SmoothManifold d)
    (J₀ J₁ : AlmostComplexField M) : ℝ → AlmostComplexField M :=
  fun t x => compatibleComplexPathStructure (J₀ x) (J₁ x) t

@[simp] theorem compatibleComplexPath_zero {d : ℕ} (M : SmoothManifold d)
    (J₀ J₁ : AlmostComplexField M) : compatibleComplexPath M J₀ J₁ 0 = J₀ := by
  funext x
  simp [compatibleComplexPath, compatibleComplexPathStructure]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem compatibleComplexPath_one {d : ℕ} (M : SmoothManifold d)
    (eta : M.Form 2) (J₀ J₁ : AlmostComplexField M)
    (h₀ : IsCompatibleAlmostComplex M eta J₀)
    (h₁ : IsCompatibleAlmostComplex M eta J₁) :
    compatibleComplexPath M J₀ J₁ 1 = J₁ := by
  funext x
  ext v
  simp only [compatibleComplexPath, compatibleComplexPathStructure,
    ContinuousLinearMap.comp_apply, compatibleComplexPathMap_one]
  rw [compatibleComplexTransport_intertwines _ _ (h₁.2.1 x) (h₀.2.1 x)]
  have hi : (compatibleComplexTransport (J₁ x) (J₀ x)).IsInvertible := by
    simpa only [compatibleComplexPathMap_one] using
      compatibleComplexPathMap_isInvertible M eta J₀ J₁ h₀ h₁ 1 parameterOne.property x
  rw [hi.self_apply_inverse]

set_option backward.isDefEq.respectTransparency false in
theorem compatibleComplexPath_sq {d : ℕ} (M : SmoothManifold d)
    (eta : M.Form 2) (J₀ J₁ : AlmostComplexField M)
    (h₀ : IsCompatibleAlmostComplex M eta J₀)
    (h₁ : IsCompatibleAlmostComplex M eta J₁) (t : ℝ) (ht : t ∈ parameterInterval)
    (x : M.Point) (v : M.Tangent x) :
    compatibleComplexPath M J₀ J₁ t x (compatibleComplexPath M J₀ J₁ t x v) = -v := by
  have hi := compatibleComplexPathMap_isInvertible M eta J₀ J₁ h₀ h₁ t ht x
  simp only [compatibleComplexPath, compatibleComplexPathStructure,
    ContinuousLinearMap.comp_apply, hi.inverse_apply_self, h₀.2.1, map_neg,
    hi.self_apply_inverse]

set_option backward.isDefEq.respectTransparency false in
theorem compatibleComplexPath_preserves_form {d : ℕ} (M : SmoothManifold d)
    (eta : M.Form 2) (J₀ J₁ : AlmostComplexField M)
    (h₀ : IsCompatibleAlmostComplex M eta J₀)
    (h₁ : IsCompatibleAlmostComplex M eta J₁) (t : ℝ) (ht : t ∈ parameterInterval)
    (x : M.Point) (u v : M.Tangent x) :
    SmoothManifold.evalTwo eta x (compatibleComplexPath M J₀ J₁ t x u)
      (compatibleComplexPath M J₀ J₁ t x v) = SmoothManifold.evalTwo eta x u v := by
  have hi := compatibleComplexPathMap_isInvertible M eta J₀ J₁ h₀ h₁ t ht x
  simp only [compatibleComplexPath, compatibleComplexPathStructure,
    ContinuousLinearMap.comp_apply]
  rw [compatibleComplexPathMap_preserves_J_form M eta J₀ J₁ h₀ h₁,
    hi.self_apply_inverse, hi.self_apply_inverse]

set_option backward.isDefEq.respectTransparency false in
theorem compatibleComplexPath_positive {d : ℕ} (M : SmoothManifold d)
    (eta : M.Form 2) (J₀ J₁ : AlmostComplexField M)
    (h₀ : IsCompatibleAlmostComplex M eta J₀)
    (h₁ : IsCompatibleAlmostComplex M eta J₁) (t : ℝ) (ht : t ∈ parameterInterval)
    (x : M.Point) (v : M.Tangent x) (hv : v ≠ 0) :
    0 < SmoothManifold.evalTwo eta x v (compatibleComplexPath M J₀ J₁ t x v) := by
  have hi := compatibleComplexPathMap_isInvertible M eta J₀ J₁ h₀ h₁ t ht x
  have hn : (compatibleComplexPathMap (J₀ x) (J₁ x) t).inverse v ≠ 0 := by
    intro hz
    have hh := hi.self_apply_inverse v
    rw [hz, map_zero] at hh
    exact hv hh.symm
  have hp := compatibleComplexPathMap_positive M eta J₀ J₁ h₀ h₁ t ht x _ hn
  simpa only [hi.self_apply_inverse, compatibleComplexPath,
    compatibleComplexPathStructure, ContinuousLinearMap.comp_apply] using hp

section Intertwining

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compatibleComplexPathMap_intertwines (G : E →L[ℝ] F)
    (K₀ K₁ : E →L[ℝ] E) (J₀ J₁ : F →L[ℝ] F)
    (h₀ : ∀ v, G (K₀ v) = J₀ (G v)) (h₁ : ∀ v, G (K₁ v) = J₁ (G v))
    (t : ℝ) (v : E) :
    G (compatibleComplexPathMap K₀ K₁ t v) =
      compatibleComplexPathMap J₀ J₁ t (G v) := by
  simp only [compatibleComplexPathMap, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    map_sub, map_smul, h₀, h₁]

theorem compatibleComplexPathMap_eq_conjugate (G : E →L[ℝ] F) (hG : G.IsInvertible)
    (K₀ K₁ : E →L[ℝ] E) (J₀ J₁ : F →L[ℝ] F)
    (h₀ : ∀ v, G (K₀ v) = J₀ (G v)) (h₁ : ∀ v, G (K₁ v) = J₁ (G v))
    (t : ℝ) :
    compatibleComplexPathMap K₀ K₁ t =
      G.inverse.comp ((compatibleComplexPathMap J₀ J₁ t).comp G) := by
  ext v
  apply hG.injective
  simp only [ContinuousLinearMap.comp_apply, hG.self_apply_inverse]
  exact compatibleComplexPathMap_intertwines G K₀ K₁ J₀ J₁ h₀ h₁ t v

/-- The total inverse also respects an invertible change of coordinates,
including where the interpolating map itself is singular. -/
theorem compatibleComplexPathMap_inverse_intertwines (G : E →L[ℝ] F)
    (hG : G.IsInvertible) (K₀ K₁ : E →L[ℝ] E) (J₀ J₁ : F →L[ℝ] F)
    (h₀ : ∀ v, G (K₀ v) = J₀ (G v)) (h₁ : ∀ v, G (K₁ v) = J₁ (G v))
    (t : ℝ) (v : E) :
    G ((compatibleComplexPathMap K₀ K₁ t).inverse v) =
      (compatibleComplexPathMap J₀ J₁ t).inverse (G v) := by
  rw [compatibleComplexPathMap_eq_conjugate G hG K₀ K₁ J₀ J₁ h₀ h₁ t,
    hG.inverse.inverse_comp_of_left, hG.inverse_comp_of_right, hG.inverse_inverse]
  simp only [ContinuousLinearMap.comp_apply, hG.self_apply_inverse]

theorem compatibleComplexPathStructure_intertwines (G : E →L[ℝ] F)
    (hG : G.IsInvertible) (K₀ K₁ : E →L[ℝ] E) (J₀ J₁ : F →L[ℝ] F)
    (h₀ : ∀ v, G (K₀ v) = J₀ (G v)) (h₁ : ∀ v, G (K₁ v) = J₁ (G v))
    (t : ℝ) (v : E) :
    G (compatibleComplexPathStructure K₀ K₁ t v) =
      compatibleComplexPathStructure J₀ J₁ t (G v) := by
  simp only [compatibleComplexPathStructure, ContinuousLinearMap.comp_apply]
  rw [compatibleComplexPathMap_intertwines G K₀ K₁ J₀ J₁ h₀ h₁,
    h₀, compatibleComplexPathMap_inverse_intertwines G hG K₀ K₁ J₀ J₁ h₀ h₁]

end Intertwining

set_option backward.isDefEq.respectTransparency false in
/-- The explicit path is intrinsic: its spatial chart expression is the
same conjugation formula applied to the chart expressions of its inputs. -/
theorem almostComplexInChart_compatibleComplexPath {n : ℕ}
    (M : SmoothManifold (2 * n)) (a : M.Point) (J₀ J₁ : AlmostComplexField M)
    (t : ℝ) (y : Model (2 * n)) (hy : y ∈ (chartAt (Model (2 * n)) a).target) :
    almostComplexInChart M a (compatibleComplexPath M J₀ J₁ t) y =
      compatibleComplexPathStructure (almostComplexInChart M a J₀ y)
        (almostComplexInChart M a J₁ y) t := by
  let G : Model (2 * n) →L[ℝ] Model (2 * n) := M.inverseChartTangentMap a y
  let K₀ : Model (2 * n) →L[ℝ] Model (2 * n) :=
    J₀ ((chartAt (Model (2 * n)) a).symm y)
  let K₁ : Model (2 * n) →L[ℝ] Model (2 * n) :=
    J₁ ((chartAt (Model (2 * n)) a).symm y)
  have hG : G.IsInvertible := inverseChartTangentMap_isInvertible M a y hy
  have hk₀ : ∀ v, G (almostComplexInChart M a J₀ y v) = K₀ (G v) :=
    inverseChartTangentMap_almostComplexInChart M a J₀ y hy
  have hk₁ : ∀ v, G (almostComplexInChart M a J₁ y v) = K₁ (G v) :=
    inverseChartTangentMap_almostComplexInChart M a J₁ y hy
  apply ContinuousLinearMap.ext
  intro v
  apply hG.injective
  calc
    G (almostComplexInChart M a (compatibleComplexPath M J₀ J₁ t) y v) =
        compatibleComplexPathStructure K₀ K₁ t (G v) :=
      inverseChartTangentMap_almostComplexInChart M a _ y hy v
    _ = G (compatibleComplexPathStructure (almostComplexInChart M a J₀ y)
        (almostComplexInChart M a J₁ y) t v) :=
      (compatibleComplexPathStructure_intertwines G hG _ _ K₀ K₁ hk₀ hk₁ t v).symm

set_option backward.isDefEq.respectTransparency false in
theorem compatibleComplexPathMap_inChart_isInvertible {n : ℕ}
    (M : SmoothManifold (2 * n)) (eta : M.Form 2) (a : M.Point)
    (J₀ J₁ : AlmostComplexField M)
    (h₀ : IsCompatibleAlmostComplex M eta J₀)
    (h₁ : IsCompatibleAlmostComplex M eta J₁) (t : ℝ) (ht : t ∈ parameterInterval)
    (y : Model (2 * n)) (hy : y ∈ (chartAt (Model (2 * n)) a).target) :
    (compatibleComplexPathMap (almostComplexInChart M a J₀ y)
      (almostComplexInChart M a J₁ y) t).IsInvertible := by
  let G : Model (2 * n) →L[ℝ] Model (2 * n) := M.inverseChartTangentMap a y
  let K₀ : Model (2 * n) →L[ℝ] Model (2 * n) :=
    J₀ ((chartAt (Model (2 * n)) a).symm y)
  let K₁ : Model (2 * n) →L[ℝ] Model (2 * n) :=
    J₁ ((chartAt (Model (2 * n)) a).symm y)
  have hG : G.IsInvertible := inverseChartTangentMap_isInvertible M a y hy
  have hk₀ : ∀ v, G (almostComplexInChart M a J₀ y v) = K₀ (G v) :=
    inverseChartTangentMap_almostComplexInChart M a J₀ y hy
  have hk₁ : ∀ v, G (almostComplexInChart M a J₁ y v) = K₁ (G v) :=
    inverseChartTangentMap_almostComplexInChart M a J₁ y hy
  rw [compatibleComplexPathMap_eq_conjugate G hG _ _ K₀ K₁ hk₀ hk₁ t]
  have hi : (compatibleComplexPathMap K₀ K₁ t).IsInvertible :=
    compatibleComplexPathMap_isInvertible M eta J₀ J₁ h₀ h₁ t ht _
  exact hG.inverse.comp (hi.comp hG)

theorem contDiffOn_compatibleComplexPathMap {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}
    {J₀ J₁ : E → Model d →L[ℝ] Model d} {time : E → ℝ}
    (h₀ : ContDiffOn ℝ ∞ J₀ U) (h₁ : ContDiffOn ℝ ∞ J₁ U)
    (ht : ContDiffOn ℝ ∞ time U) :
    ContDiffOn ℝ ∞ (fun p => compatibleComplexPathMap (J₀ p) (J₁ p) (time p)) U := by
  exact ((contDiffOn_const.sub (ht.div_const 2)).smul
    (contDiffOn_const (c := ContinuousLinearMap.id ℝ (Model d)))).sub
      ((ht.div_const 2).smul (h₁.clm_comp h₀))

theorem contDiffOn_compatibleComplexPathStructure {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} (hU : IsOpen U)
    {J₀ J₁ : E → Model d →L[ℝ] Model d} {time : E → ℝ}
    (h₀ : ContDiffOn ℝ ∞ J₀ U) (h₁ : ContDiffOn ℝ ∞ J₁ U)
    (ht : ContDiffOn ℝ ∞ time U)
    (hinv : ∀ p ∈ U, (compatibleComplexPathMap (J₀ p) (J₁ p) (time p)).IsInvertible) :
    ContDiffOn ℝ ∞ (fun p => compatibleComplexPathStructure (J₀ p) (J₁ p) (time p)) U := by
  have hA := contDiffOn_compatibleComplexPathMap h₀ h₁ ht
  intro p hp
  have hAa := hA.contDiffAt (hU.mem_nhds hp)
  have hi₀ : ContDiffAt ℝ ∞
      (ContinuousLinearMap.inverse : (Model d →L[ℝ] Model d) → Model d →L[ℝ] Model d)
      (compatibleComplexPathMap (J₀ p) (J₁ p) (time p)) :=
    (hinv p hp).contDiffAt_map_inverse
  have hi : ContDiffAt ℝ ∞
      (fun p => (compatibleComplexPathMap (J₀ p) (J₁ p) (time p)).inverse) p :=
    hi₀.comp (g := ContinuousLinearMap.inverse)
      (f := fun p => compatibleComplexPathMap (J₀ p) (J₁ p) (time p)) p hAa
  exact (hAa.clm_comp ((h₀.contDiffAt (hU.mem_nhds hp)).clm_comp hi)).contDiffWithinAt

set_option backward.isDefEq.respectTransparency false in
/-- Polynomial dependence followed by smooth inversion gives a jointly
smooth extension near the interval on each whole spatial chart. The open
neighborhood is the pointwise inversion locus, not a uniform time collar. -/
theorem smoothNearInterval_compatibleComplexPath {n : ℕ}
    (M : SmoothManifold (2 * n)) (eta : M.Form 2) (J₀ J₁ : AlmostComplexField M)
    (h₀ : IsCompatibleAlmostComplex M eta J₀)
    (h₁ : IsCompatibleAlmostComplex M eta J₁) (a : M.Point) :
    SmoothNearInterval (chartAt (Model (2 * n)) a).target
      (fun p => almostComplexInChart M a (compatibleComplexPath M J₀ J₁ p.1) p.2) := by
  let V := (chartAt (Model (2 * n)) a).target
  let W : Set (ℝ × Model (2 * n)) := univ ×ˢ V
  let K₀ : ℝ × Model (2 * n) → Model (2 * n) →L[ℝ] Model (2 * n) :=
    fun p => almostComplexInChart M a J₀ p.2
  let K₁ : ℝ × Model (2 * n) → Model (2 * n) →L[ℝ] Model (2 * n) :=
    fun p => almostComplexInChart M a J₁ p.2
  let A : ℝ × Model (2 * n) → Model (2 * n) →L[ℝ] Model (2 * n) :=
    fun p => compatibleComplexPathMap (K₀ p) (K₁ p) p.1
  have hW : IsOpen W := isOpen_univ.prod (chartAt (Model (2 * n)) a).open_target
  have hk₀ : ContDiffOn ℝ ∞ K₀ W :=
    (h₀.1 a).comp contDiffOn_snd (fun _ hp => hp.2)
  have hk₁ : ContDiffOn ℝ ∞ K₁ W :=
    (h₁.1 a).comp contDiffOn_snd (fun _ hp => hp.2)
  have hA : ContDiffOn ℝ ∞ A W :=
    contDiffOn_compatibleComplexPathMap hk₀ hk₁ contDiffOn_fst
  let U := W ∩ A ⁻¹' {L | L.IsInvertible}
  have hU : IsOpen U := hA.continuousOn.isOpen_inter_preimage hW
    ContinuousLinearMap.isOpen_setOfPred_isInvertible
  refine ⟨U, hU, ?_, ?_⟩
  · intro p hp
    exact ⟨⟨mem_univ _, hp.2⟩,
      compatibleComplexPathMap_inChart_isInvertible M eta a J₀ J₁ h₀ h₁ p.1 hp.1 p.2 hp.2⟩
  · have hk : ContDiffOn ℝ ∞
        (fun p => compatibleComplexPathStructure (K₀ p) (K₁ p) p.1) U :=
      contDiffOn_compatibleComplexPathStructure hU (hk₀.mono inter_subset_left)
        (hk₁.mono inter_subset_left) contDiffOn_fst (fun _ hp => hp.2)
    exact hk.congr (fun p hp =>
      almostComplexInChart_compatibleComplexPath M a J₀ J₁ p.1 p.2 hp.1.2)

set_option backward.isDefEq.respectTransparency false in
theorem compatibleComplexPath_compatible {n : ℕ} (M : SmoothManifold (2 * n))
    (eta : M.Form 2) (J₀ J₁ : AlmostComplexField M)
    (h₀ : IsCompatibleAlmostComplex M eta J₀)
    (h₁ : IsCompatibleAlmostComplex M eta J₁) (t : ℝ) (ht : t ∈ parameterInterval) :
    IsCompatibleAlmostComplex M eta (compatibleComplexPath M J₀ J₁ t) := by
  refine ⟨?_, compatibleComplexPath_sq M eta J₀ J₁ h₀ h₁ t ht,
    compatibleComplexPath_preserves_form M eta J₀ J₁ h₀ h₁ t ht,
    compatibleComplexPath_positive M eta J₀ J₁ h₀ h₁ t ht⟩
  intro a
  obtain ⟨U, _, hi, hd⟩ := smoothNearInterval_compatibleComplexPath M eta J₀ J₁ h₀ h₁ a
  exact hd.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hy => hi ⟨ht, hy⟩)

/-- Compatibility itself supplies the smooth compatible path, with
literal endpoint agreement and genuine smooth extensions at both ends. -/
theorem exists_smooth_compatibleComplexPath {n : ℕ} (M : SmoothManifold (2 * n))
    (eta : M.Form 2) (J₀ J₁ : AlmostComplexField M)
    (h₀ : IsCompatibleAlmostComplex M eta J₀)
    (h₁ : IsCompatibleAlmostComplex M eta J₁) :
    ∃ J : ℝ → AlmostComplexField M, J 0 = J₀ ∧ J 1 = J₁ ∧
      (∀ t ∈ parameterInterval, IsCompatibleAlmostComplex M eta (J t)) ∧
      ∀ a, SmoothNearInterval (chartAt (Model (2 * n)) a).target
        (fun p => almostComplexInChart M a (J p.1) p.2) :=
  ⟨compatibleComplexPath M J₀ J₁, compatibleComplexPath_zero M J₀ J₁,
    compatibleComplexPath_one M eta J₀ J₁ h₀ h₁,
    compatibleComplexPath_compatible M eta J₀ J₁ h₀ h₁,
    smoothNearInterval_compatibleComplexPath M eta J₀ J₁ h₀ h₁⟩

end FsFltz.Geometry
