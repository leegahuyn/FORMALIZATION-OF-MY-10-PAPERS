import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.CompactModularCore
import PrimalitySheafVerification.ManuscriptAudit.HighInfinityCusp

/-!
# The three high cusp charts of the level-two modular quotient

The matrices `1`, `S`, and `T*S` give the cusp coordinates at infinity,
zero, and one. Modulo two their first columns are the three distinct
nonzero vectors. At a height above `Y ≥ 1` the projected neighborhoods
are disjoint and each chart has exactly the even translation relation.
The three neighborhoods exhaust all the high horoball images.
-/

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane

namespace ManuscriptAudit.ThreeCuspNeighborhoods

open LiteralCuspTruncation (GammaTwo OrbitQuotient orbitPoint)
open CompactModularCore (Reduced reduceTwo mem_gamma_iff_reduced_one)
open ModularGroup (S T)

noncomputable section

def chart (i : Fin 3) : SL(2, ℤ) := ![1, S, T * S] i

def neighborhood (Y : ℝ) (i : Fin 3) : Set OrbitQuotient :=
  (fun z : ℍ => orbitPoint (chart i • z)) '' {z : ℍ | Y < z.im}

private def firstColumn (a : Reduced) : ZMod 2 × ZMod 2 := (a 0 0, a 1 0)

private theorem reduce_entry (g : SL(2, ℤ)) (i j : Fin 2) :
    reduceTwo g i j = (g i j : ZMod 2) := rfl

private theorem chart_column_0 : firstColumn (reduceTwo (chart 0)) = (1, 0) := by decide

private theorem chart_column_1 : firstColumn (reduceTwo (chart 1)) = (0, 1) := by decide

private theorem chart_column_2 : firstColumn (reduceTwo (chart 2)) = (1, 1) := by decide

private theorem chart_column_injective :
    Function.Injective (fun i : Fin 3 => firstColumn (reduceTwo (chart i))) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [chart_column_0, chart_column_1, chart_column_2]

private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hv := ZMod.val_lt a
  have h : a.val = 0 ∨ a.val = 1 := by omega
  rcases h with h | h
  · left
    simpa only [h, Nat.cast_zero] using (ZMod.natCast_zmod_val a).symm
  · right
    simpa only [h, Nat.cast_one] using (ZMod.natCast_zmod_val a).symm

private theorem exists_chart_of_column (a : Reduced) :
    ∃ i : Fin 3, firstColumn a = firstColumn (reduceTwo (chart i)) := by
  rcases zmod_two_cases (a 0 0) with ha | ha <;>
    rcases zmod_two_cases (a 1 0) with hb | hb
  · exfalso
    have hd := a.det_coe
    rw [Matrix.det_fin_two, ha, hb, zero_mul, mul_zero, sub_zero] at hd
    exact zero_ne_one hd
  · exact ⟨1, by rw [chart_column_1]; exact Prod.ext ha hb⟩
  · exact ⟨0, by rw [chart_column_0]; exact Prod.ext ha hb⟩
  · exact ⟨2, by rw [chart_column_2]; exact Prod.ext ha hb⟩

private theorem firstColumn_mul_congr (a b c : Reduced) (h : firstColumn b = firstColumn c) :
    firstColumn (a * b) = firstColumn (a * c) := by
  have h0 : b 0 0 = c 0 0 := congrArg Prod.fst h
  have h1 : b 1 0 = c 1 0 := congrArg Prod.snd h
  have he (i : Fin 2) : (a * b) i 0 = (a * c) i 0 := by
    change (a.1 * b.1) i 0 = (a.1 * c.1) i 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h0, h1]
  exact Prod.ext (he 0) (he 1)

private theorem firstColumn_one : firstColumn (1 : Reduced) = (1, 0) := by decide

private theorem firstColumn_of_integral_upper (g : SL(2, ℤ)) (hc : g 1 0 = 0) :
    firstColumn (reduceTwo g) = firstColumn 1 := by
  have hdet : g 0 0 * g 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using g.det_coe
  rw [firstColumn_one]
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨ha, _⟩ | ⟨ha, _⟩
  · simp [firstColumn, reduce_entry, ha, hc]
  · simp [firstColumn, reduce_entry, ha, hc, show (-1 : ZMod 2) = 1 by decide]

private theorem exists_translation_of_reduced_column (a : Reduced)
    (h : firstColumn a = firstColumn 1) : ∃ m : ℤ, reduceTwo (T ^ m) = a := by
  have h0 : a 0 0 = 1 := congrArg Prod.fst (h.trans firstColumn_one)
  have h1 : a 1 0 = 0 := congrArg Prod.snd (h.trans firstColumn_one)
  have h11 : a 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, h0, h1, one_mul, mul_zero, sub_zero] using a.det_coe
  let m : ℤ := (a 0 1).val
  refine ⟨m, SpecialLinearGroup.ext _ _ ?_⟩
  intro i j
  rw [reduce_entry]
  change ((T ^ m).1 i j : ZMod 2) = a i j
  rw [ModularGroup.coe_T_zpow]
  fin_cases i <;> fin_cases j
  · simpa using h0.symm
  · change (m : ZMod 2) = a 0 1
    dsimp only [m]
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val (a 0 1)
  · simpa using h1.symm
  · simpa using h11.symm

/-- Every modular coordinate differs from one of the three charts by a
level-two action followed, in the cusp coordinate, by a translation. -/
theorem coordinate_factorization (g : SL(2, ℤ)) :
    ∃ (i : Fin 3) (m : ℤ) (γ : GammaTwo), g = (γ : SL(2, ℤ)) * (chart i * T ^ m) := by
  obtain ⟨i, hi⟩ := exists_chart_of_column (reduceTwo g)
  let a := chart i
  let k := a⁻¹ * g
  have hk : firstColumn (reduceTwo k) = firstColumn 1 := by
    have h := firstColumn_mul_congr (reduceTwo a)⁻¹ (reduceTwo g) (reduceTwo a) hi
    simpa only [k, map_mul, map_inv, inv_mul_cancel] using h
  obtain ⟨m, hm⟩ := exists_translation_of_reduced_column (reduceTwo k) hk
  have hred : reduceTwo g = reduceTwo (a * T ^ m) := by
    rw [map_mul, hm, ← map_mul]
    simp [k, ← mul_assoc]
  let γ := g * (a * T ^ m)⁻¹
  have hγ : γ ∈ GammaTwo := (mem_gamma_iff_reduced_one _).mpr (by
    dsimp [γ]
    rw [map_mul, map_inv, hred, mul_inv_cancel])
  refine ⟨i, m, ⟨γ, hγ⟩, ?_⟩
  change g = γ * (a * T ^ m)
  simp [γ, mul_assoc]

theorem highOrbits_eq_three_neighborhoods (Y : ℝ) :
    CompactModularCore.highOrbits Y = ⋃ i : Fin 3, neighborhood Y i := by
  ext q
  constructor
  · rintro ⟨g, z, hz, hq⟩
    obtain ⟨i, m, γ, hg⟩ := coordinate_factorization g
    apply Set.mem_iUnion.2
    refine ⟨i, T ^ m • z, ?_, ?_⟩
    · simpa only [ModularGroup.im_T_zpow_smul] using hz
    · have hγ : γ • (chart i • (T ^ m • z)) = g • z := by
        change (γ : SL(2, ℤ)) • (chart i • (T ^ m • z)) = g • z
        rw [hg, mul_smul, mul_smul]
      exact (Quotient.sound ⟨γ, hγ⟩).symm.trans hq
  · intro h
    obtain ⟨i, z, hz, hq⟩ := Set.mem_iUnion.1 h
    exact ⟨chart i, z, hz, hq⟩

theorem high_chart_eq_iff {Y : ℝ} (hY : 1 ≤ Y) {i j : Fin 3} {z w : ℍ}
    (hz : Y < z.im) (hw : Y < w.im) :
    orbitPoint (chart j • w) = orbitPoint (chart i • z) ↔
      i = j ∧ ∃ m : ℤ, (w : ℂ) = (z : ℂ) + 2 * (m : ℂ) := by
  constructor
  · intro h
    have hOrb : ∃ γ : GammaTwo, γ • (chart i • z) = chart j • w := Quotient.exact h
    obtain ⟨γ, hγ⟩ := hOrb
    have hγred : reduceTwo (γ : SL(2, ℤ)) = 1 :=
      (mem_gamma_iff_reduced_one _).mp γ.2
    let k := (chart j)⁻¹ * ((γ : SL(2, ℤ)) * chart i)
    have hAct : k • z = w := by
      change (γ : SL(2, ℤ)) • (chart i • z) = chart j • w at hγ
      dsimp [k]
      rw [mul_smul, mul_smul, hγ, ← mul_smul, inv_mul_cancel, one_smul]
    have hk : k 1 0 = 0 := HighInfinityCusp.bottom_left_zero_of_high_image hY k hz (by
      rw [hAct]
      exact hw)
    have hProd : reduceTwo (chart j) * reduceTwo k = reduceTwo (chart i) := by
      rw [← map_mul]
      have he : chart j * k = (γ : SL(2, ℤ)) * chart i := by simp [k, ← mul_assoc]
      rw [he, map_mul, hγred, one_mul]
    have hCol := firstColumn_mul_congr (reduceTwo (chart j)) (reduceTwo k) 1
      (firstColumn_of_integral_upper k hk)
    rw [hProd, mul_one] at hCol
    have hij : i = j := chart_column_injective hCol
    subst j
    have hkred : reduceTwo k = 1 := by simp [k, map_mul, map_inv, hγred]
    let k' : GammaTwo := ⟨k, (mem_gamma_iff_reduced_one _).mpr hkred⟩
    have hkAct : k' • z = w := hAct
    have hk0 : (k' : SL(2, ℤ)) 1 0 = 0 := hk
    obtain ⟨m, hm⟩ := HighInfinityCusp.even_translate_of_bottom_left_zero k' z hk0
    exact ⟨rfl, m, hkAct ▸ hm⟩
  · rintro ⟨rfl, m, hm⟩
    obtain ⟨k, hk⟩ := (HighInfinityCusp.high_orbit_iff_even_translate hY hz hw).mpr ⟨m, hm⟩
    have hkred : reduceTwo (k : SL(2, ℤ)) = 1 := (mem_gamma_iff_reduced_one _).mp k.2
    let γ := chart i * ((k : SL(2, ℤ)) * (chart i)⁻¹)
    have hγ : γ ∈ GammaTwo := (mem_gamma_iff_reduced_one _).mpr (by
      simp [γ, map_mul, map_inv, hkred])
    refine Quotient.sound ⟨⟨γ, hγ⟩, ?_⟩
    change γ • (chart i • z) = chart i • w
    change (k : SL(2, ℤ)) • z = w at hk
    rw [← mul_smul, show γ * chart i = chart i * (k : SL(2, ℤ)) by simp [γ, mul_assoc],
      mul_smul, hk]

theorem neighborhoods_disjoint {Y : ℝ} (hY : 1 ≤ Y) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (neighborhood Y i) (neighborhood Y j) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨z, hz, hzq⟩ ⟨w, hw, hwq⟩
  exact hij ((high_chart_eq_iff hY hz hw).mp (hwq.trans hzq.symm)).1

theorem compact_core_eq_complement_three_neighborhoods (Y : ℝ) :
    CompactModularCore.core Y = (⋃ i : Fin 3, neighborhood Y i)ᶜ := by
  rw [CompactModularCore.core_eq_complement_highOrbits, highOrbits_eq_three_neighborhoods]

end

end ManuscriptAudit.ThreeCuspNeighborhoods

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ThreeCuspNeighborhoods.coordinate_factorization,
      ``ManuscriptAudit.ThreeCuspNeighborhoods.highOrbits_eq_three_neighborhoods,
      ``ManuscriptAudit.ThreeCuspNeighborhoods.high_chart_eq_iff,
      ``ManuscriptAudit.ThreeCuspNeighborhoods.neighborhoods_disjoint,
      ``ManuscriptAudit.ThreeCuspNeighborhoods.compact_core_eq_complement_three_neighborhoods] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
