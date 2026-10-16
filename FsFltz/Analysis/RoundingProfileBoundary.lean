import FsFltz.Analytic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Boundary faces of arbitrary rounding profiles

These lemmas apply to every native `RoundingProfile`, rather than only to a
particular construction. They implement `sec:initial` of
`geoemtric-part-fsf.tex`, lines 329–341, and the unchanged-face argument in
`prop:allinitial` of `geometric-part-fsf-proof.tex`, lines 909–920.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace FsFltz
namespace RoundingProfile

variable {eps : ℝ} (m : RoundingProfile eps)

/-- At contact with the first-coordinate lower bound the full differential is
exactly the first-coordinate projection. This includes flat junctions. -/
lemma fderiv_eq_fst_of_eq (p : ℝ × ℝ) (hp : m.toFun p = p.1) :
    fderiv ℝ m.toFun p = ContinuousLinearMap.fst ℝ ℝ ℝ := by
  have hmin : IsMinOn (fun q : ℝ × ℝ => m.toFun q - q.1) univ p := by
    apply isMinOn_univ_iff.mpr
    intro q
    have h := (le_max_left q.1 q.2).trans (m.lower q)
    simp only [hp, sub_self]
    exact sub_nonneg.mpr h
  have hz := (hmin.isLocalMin (by simp)).hasFDerivAt_eq_zero
    (((m.smooth.differentiable (by simp)) p).hasFDerivAt.sub hasFDerivAt_fst)
  exact sub_eq_zero.mp hz

/-- At contact with the second-coordinate lower bound the full differential
is exactly the second-coordinate projection. -/
lemma fderiv_eq_snd_of_eq (p : ℝ × ℝ) (hp : m.toFun p = p.2) :
    fderiv ℝ m.toFun p = ContinuousLinearMap.snd ℝ ℝ ℝ := by
  have hmin : IsMinOn (fun q : ℝ × ℝ => m.toFun q - q.2) univ p := by
    apply isMinOn_univ_iff.mpr
    intro q
    have h := (le_max_right q.1 q.2).trans (m.lower q)
    simp only [hp, sub_self]
    exact sub_nonneg.mpr h
  have hz := (hmin.isLocalMin (by simp)).hasFDerivAt_eq_zero
    (((m.smooth.differentiable (by simp)) p).hasFDerivAt.sub hasFDerivAt_snd)
  exact sub_eq_zero.mp hz

lemma hasDerivAt_first (x y : ℝ) :
    HasDerivAt (fun t => m.toFun (t, y)) (fderiv ℝ m.toFun (x, y) (1, 0)) x := by
  exact (((m.smooth.differentiable (by simp)) (x, y)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)))

lemma hasDerivAt_second (x y : ℝ) :
    HasDerivAt (fun t => m.toFun (x, t)) (fderiv ℝ m.toFun (x, y) (0, 1)) y := by
  exact (((m.smooth.differentiable (by simp)) (x, y)).hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)))

lemma monotone_first (y : ℝ) : Monotone (fun x => m.toFun (x, y)) :=
  monotone_of_hasDerivAt_nonneg (fun x => m.hasDerivAt_first x y)
    (fun x => m.partialFirst_nonneg (x, y))

lemma monotone_second (x : ℝ) : Monotone (fun y => m.toFun (x, y)) :=
  monotone_of_hasDerivAt_nonneg (fun y => m.hasDerivAt_second x y)
    (fun y => m.partialSecond_nonneg (x, y))

/-- The zero level outside the first strict band inequality lies on the
unchanged second-coordinate face. -/
lemma second_eq_zero_of_zero_of_first_le_neg_eps (heps : 0 < eps)
    (p : ℝ × ℝ) (hp : m.toFun p = 0) (hx : p.1 ≤ -eps) (hy : p.2 ≤ 0) :
    p.2 = 0 := by
  rcases p with ⟨x, y⟩
  change m.toFun (x, y) = 0 at hp
  change x ≤ -eps at hx
  change y ≤ 0 at hy
  change y = 0
  by_contra hne
  have hylt : y < 0 := lt_of_le_of_ne hy hne
  have hx0 : x ≤ 0 := by linarith
  have hq : m.toFun (x, 0) = 0 := by
    rw [m.exact_away (x, 0) (by
      simp only [sub_zero, abs_of_nonpos hx0]
      linarith)]
    exact max_eq_right hx0
  have hmin : IsMinOn (fun t => m.toFun (x, t)) (Ioi y) 0 := by
    intro t ht
    change m.toFun (x, 0) ≤ m.toFun (x, t)
    rw [hq, ← hp]
    exact m.monotone_second x ht.le
  have hd := m.hasDerivAt_second x 0
  rw [m.fderiv_eq_snd_of_eq (x, 0) hq] at hd
  have hz : (1 : ℝ) = 0 :=
    (hmin.isLocalMin (Ioi_mem_nhds hylt)).hasDerivAt_eq_zero (by simpa using hd)
  norm_num at hz

/-- Symmetric unchanged-face classification outside the second strict band
inequality. -/
lemma first_eq_zero_of_zero_of_second_le_neg_eps (heps : 0 < eps)
    (p : ℝ × ℝ) (hp : m.toFun p = 0) (hx : p.1 ≤ 0) (hy : p.2 ≤ -eps) :
    p.1 = 0 := by
  rcases p with ⟨x, y⟩
  change m.toFun (x, y) = 0 at hp
  change x ≤ 0 at hx
  change y ≤ -eps at hy
  change x = 0
  by_contra hne
  have hxlt : x < 0 := lt_of_le_of_ne hx hne
  have hy0 : y ≤ 0 := by linarith
  have hq : m.toFun (0, y) = 0 := by
    rw [m.exact_away (0, y) (by
      simp only [zero_sub, abs_neg, abs_of_nonpos hy0]
      linarith)]
    exact max_eq_left hy0
  have hmin : IsMinOn (fun t => m.toFun (t, y)) (Ioi x) 0 := by
    intro t ht
    change m.toFun (0, y) ≤ m.toFun (t, y)
    rw [hq, ← hp]
    exact m.monotone_first y ht.le
  have hd := m.hasDerivAt_first 0 y
  rw [m.fderiv_eq_fst_of_eq (0, y) hq] at hd
  have hz : (1 : ℝ) = 0 :=
    (hmin.isLocalMin (Ioi_mem_nhds hxlt)).hasDerivAt_eq_zero (by simpa using hd)
  norm_num at hz

end RoundingProfile
end FsFltz
