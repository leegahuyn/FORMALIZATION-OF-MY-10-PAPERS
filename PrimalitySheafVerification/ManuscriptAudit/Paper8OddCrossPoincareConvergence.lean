import Lean.Util.CollectAxioms
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossPoincareHeight
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaInverseWeightedVanishing
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaCuspWidths

/-! Absolute convergence of the actual odd cross-cusp row expansion in the initial half-plane. -/

namespace ManuscriptAudit.Paper8OddCrossPoincareConvergence

open UpperHalfPlane Paper8OddCrossCuspNormalization Paper8NormalizedKloostermanRows
open Paper8OddCrossScaledRows Paper8OddCrossPoincareKernel Paper8OddCrossPoincareHeight
open Paper8OddCrossCuspActualMultiplier Paper8EtaPhaseCocycle Paper8EtaHalfWeightPhase
open Paper8ActualEtaSquaredModularity Paper8OddCrossCuspRows Paper8EtaCuspWidths
open Paper8EtaInverseWeightedVanishing (levelCharacter_sq)
open scoped MatrixGroups

noncomputable section

abbrev CrossIndex := Σ D : ℕ, CrossRow (D + 1) × ℤ

private abbrev MajorantIndex := Σ D : ℕ, Fin (D + 1) × ℤ

private def rowIndex {D : ℕ} (hD : 0 < D) (A : CrossRow D) : Fin D :=
  (rowsEquiv hD ((crossRowsEquiv hD (crossRow_odd A)).symm A)).1

private theorem rowIndex_injective {D : ℕ} (hD : 0 < D) :
    Function.Injective (rowIndex hD) := by
  intro A B h
  have hEq : rowsEquiv hD ((crossRowsEquiv hD (crossRow_odd A)).symm A) =
      rowsEquiv hD ((crossRowsEquiv hD (crossRow_odd B)).symm B) := by
    apply Subtype.ext
    change rowIndex hD A = rowIndex hD B
    exact h
  exact (crossRowsEquiv hD (crossRow_odd A)).symm.injective ((rowsEquiv hD).injective hEq)

private def majorantIndex : CrossIndex → MajorantIndex
  | ⟨D, A, n⟩ => ⟨D, rowIndex (Nat.succ_pos D) A, n⟩

private theorem majorantIndex_injective : Function.Injective majorantIndex := by
  rintro ⟨D, A, n⟩ ⟨E, B, m⟩ h
  have hD : D = E := congrArg Sigma.fst h
  subst E
  have hPair : (rowIndex (Nat.succ_pos D) A, n) = (rowIndex (Nat.succ_pos D) B, m) := by
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hA := rowIndex_injective (Nat.succ_pos D) (congrArg Prod.fst hPair)
  have hn : n = m := congrArg Prod.snd hPair
  subst B
  subst m
  rfl

private def shiftMajorant (σ : ℝ) (n : ℤ) : ℝ := (|(n : ℝ)| + 1) ^ (-2 * σ)

private theorem shiftMajorant_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (shiftMajorant σ) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 (2 * σ)).2 (by linarith)
  have hn : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-2 * σ)) := h.congr fun n => by
    rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1), one_div,
      ← Real.rpow_neg (by positivity : 0 ≤ (n : ℝ) + 1), neg_mul]
  apply summable_int_iff_summable_nat_and_neg.2
  exact ⟨by simpa [shiftMajorant, abs_of_nonneg] using hn,
    by simpa [shiftMajorant, abs_of_nonneg] using hn⟩

private def crossMajorant (σ : ℝ) (i : MajorantIndex) : ℝ :=
  ((i.1 : ℝ) + 1) ^ (-2 * σ) * shiftMajorant σ i.2.2

private theorem crossMajorant_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (crossMajorant σ) := by
  let b := shiftMajorant σ
  have hb : Summable b := shiftMajorant_summable hσ
  have hProd (D : ℕ) : Summable
      (fun p : Fin (D + 1) × ℤ => ((D : ℝ) + 1) ^ (-2 * σ) * b p.2) :=
    (summable_prod_of_nonneg (fun _ => by
      dsimp only [b, shiftMajorant]
      positivity)).2 ⟨fun _ => hb.mul_left _, by
        exact Summable.of_finite⟩
  have hReduce (D : ℕ) : (∑' p : Fin (D + 1) × ℤ,
      ((D : ℝ) + 1) ^ (-2 * σ) * b p.2) =
      (∑' n, b n) * ((D : ℝ) + 1) ^ (1 - 2 * σ) := by
    have hD : 0 < (D : ℝ) + 1 := by positivity
    rw [(hProd D).tsum_prod]
    simp only [tsum_mul_left, tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    rw [show (1 - 2 * σ : ℝ) = 1 + (-2 * σ) by ring, Real.rpow_add hD, Real.rpow_one]
    ring
  have hs : Summable (fun D : ℕ => ((D : ℝ) + 1) ^ (1 - 2 * σ)) :=
    ((Real.summable_one_div_nat_add_rpow 1 (2 * σ - 1)).2 (by linarith)).congr fun D => by
      rw [abs_of_nonneg (by positivity : 0 ≤ (D : ℝ) + 1), one_div,
        ← Real.rpow_neg (by positivity : 0 ≤ (D : ℝ) + 1)]
      congr 1
      ring
  apply (summable_sigma_of_nonneg (fun i => by
    unfold crossMajorant shiftMajorant
    positivity)).2
  exact ⟨hProd, (hs.mul_left _).congr (fun D => (hReduce D).symm)⟩

private theorem scaledCross_rpow_le {σ : ℝ} (hσ : 0 ≤ σ) {D : ℕ} (hD : 0 < D)
    (A : CrossRow D) (z : ℍ) (n : ℤ) :
    (scaledCrossMatrix A • translatePoint n z).im ^ σ ≤
      ((z.im * crossHeightConstant z) ^ σ * (2 : ℝ) ^ (-2 * σ)) *
        ((D : ℝ) ^ (-2 * σ) * shiftMajorant σ n) := by
  have hD0 : 0 ≤ (D : ℝ) := by positivity
  have hn0 : 0 ≤ |(n : ℝ)| + 1 := by positivity
  have hC : 0 ≤ z.im * crossHeightConstant z := (mul_pos z.im_pos (crossHeightConstant_pos z)).le
  have h := Real.rpow_le_rpow (scaledCrossMatrix A • translatePoint n z : ℍ).im_pos.le
    (scaledCross_translate_height_le hD A z n) hσ
  refine h.trans_eq ?_
  rw [Real.div_rpow hC (by positivity), Real.mul_rpow (sq_nonneg _) (sq_nonneg _),
    ← Real.rpow_natCast_mul (by positivity : 0 ≤ 2 * (D : ℝ)) 2 σ,
    ← Real.rpow_natCast_mul hn0 2 σ,
    show (((2 : ℕ) : ℝ) * σ) = 2 * σ by norm_num,
    Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) hD0]
  unfold shiftMajorant
  rw [show (-2 * σ : ℝ) = -(2 * σ) by ring, Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ)),
    Real.rpow_neg hD0, Real.rpow_neg hn0]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

def oddCrossSeed (s : ℂ) (z : ℍ) (i : CrossIndex) : ℂ :=
  let w : ℍ := scaledCrossMatrix i.2.1 • translatePoint i.2.2 z
  (w.im : ℂ) ^ s * exponentialPhase ((oddInfinityFrequency : ℂ) * (w : ℂ))

private theorem oddCrossSeed_norm_le (s : ℂ) (z : ℍ) (i : CrossIndex) :
    ‖oddCrossSeed s z i‖ ≤ (scaledCrossMatrix i.2.1 • translatePoint i.2.2 z : ℍ).im ^ s.re := by
  let w : ℍ := scaledCrossMatrix i.2.1 • translatePoint i.2.2 z
  change ‖(w.im : ℂ) ^ s * exponentialPhase ((oddInfinityFrequency : ℂ) * (w : ℂ))‖ ≤ w.im ^ s.re
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos w.im_pos, exponentialPhase, Complex.norm_exp]
  apply mul_le_of_le_one_right (Real.rpow_nonneg w.im_pos.le _)
  apply Real.exp_le_one_iff.mpr
  have hRe : (2 * (Real.pi : ℂ) * Complex.I * ((oddInfinityFrequency : ℂ) * (w : ℂ))).re =
      -(2 * Real.pi * oddInfinityFrequency * w.im) := by
    norm_num [Complex.mul_re, Complex.mul_im] <;> ring
  rw [hRe]
  exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
    (by norm_num [oddInfinityFrequency])) w.im_pos.le)

theorem oddCrossSeries_summable (s : ℂ) (hs : 1 < s.re) (z : ℍ)
    (phase : CrossIndex → ℂ) (hPhase : ∀ i, ‖phase i‖ ≤ 1) :
    Summable (fun i => ‖phase i * oddCrossSeed s z i‖) := by
  have hMajorant := (crossMajorant_summable hs).comp_injective majorantIndex_injective
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    (hMajorant.mul_left ((z.im * crossHeightConstant z) ^ s.re * (2 : ℝ) ^ (-2 * s.re)))
  rintro ⟨D, A, n⟩
  rw [norm_mul]
  calc
    _ ≤ ‖oddCrossSeed s z ⟨D, A, n⟩‖ := mul_le_of_le_one_left (norm_nonneg _) (hPhase ⟨D, A, n⟩)
    _ ≤ _ := (oddCrossSeed_norm_le s z ⟨D, A, n⟩).trans
      (by
        simpa [crossMajorant, majorantIndex, Function.comp_def] using
          scaledCross_rpow_le (show 0 ≤ s.re by linarith) (Nat.succ_pos D) A z n)

def rightCuspStabilizer (n : ℤ) : CongruenceSubgroup.Gamma0 4 :=
  ⟨ModularGroup.S * ModularGroup.T ^ (4 * n) * ModularGroup.S⁻¹,
    (conjugatedTranslation_mem_iff 4 ModularGroup.S (4 * n)).2
      ⟨ModularGroup.S 1 0 ^ 2 * n, by ring⟩⟩

def actualCrossPhase (z : ℍ) (i : CrossIndex) : ℂ :=
  let q : ℍ := realDiagonalWidthFour • z
  (starRingEnd ℂ) (oddEtaPhase
    (crossGroupElement i.2.1 * rightCuspStabilizer i.2.2) (ModularGroup.S • q)) *
    (starRingEnd ℂ) (negativeSquareRootPhase ModularGroup.S q)

private theorem oddEtaPhase_norm (g : CongruenceSubgroup.Gamma0 4) (z : ℍ) :
    ‖oddEtaPhase g z‖ = 1 := by
  have h : ‖(levelCharacter g : ℂ)‖ ^ 2 = 1 := by
    rw [← norm_pow, levelCharacter_sq, norm_one]
  have hC : ‖(levelCharacter g : ℂ)‖ = 1 := by
    nlinarith [norm_nonneg (levelCharacter g : ℂ)]
  rw [oddEtaPhase, norm_mul, hC, negativePhase_norm, one_mul]

private theorem negativeSquareRootPhase_norm (g : SL(2, ℤ)) (z : ℍ) :
    ‖negativeSquareRootPhase g z‖ = 1 := by
  let d := denominator g z
  have h := denominator_ne_zero g z
  have hd : 0 < ‖d‖ := norm_pos_iff.mpr h
  have hS : ‖Complex.sqrt d‖ = Real.sqrt ‖d‖ := by
    rw [sqrt_eq_exp h, Complex.norm_exp, Complex.div_ofNat_re, Complex.log_re,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos hd]
    congr 1
    ring
  have hD : 0 < Real.sqrt ‖d‖ := Real.sqrt_pos.2 hd
  change ‖(Complex.sqrt d / (Real.sqrt ‖d‖ : ℂ)) * ((‖d‖ : ℂ) / d)‖ = 1
  rw [norm_mul, norm_div, norm_div, hS, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hd, abs_of_pos hD,
    div_self hd.ne', div_self hD.ne', mul_one]

theorem actualCrossPhase_norm (z : ℍ) (i : CrossIndex) :
    ‖actualCrossPhase z i‖ = 1 := by
  rw [actualCrossPhase, norm_mul, Complex.norm_conj, Complex.norm_conj,
    oddEtaPhase_norm, negativeSquareRootPhase_norm, one_mul]

theorem actualOddCrossSeries_summable (s : ℂ) (hs : 1 < s.re) (z : ℍ) :
    Summable (fun i => ‖actualCrossPhase z i * oddCrossSeed s z i‖) :=
  oddCrossSeries_summable s hs z _ (fun i => (actualCrossPhase_norm z i).le)

instance : Countable CrossIndex :=
  Function.Injective.countable (f := majorantIndex) majorantIndex_injective

theorem exists_summable_crossMajorant_on_unit_strip (s : ℂ) (hs : 1 < s.re) {y : ℝ} (hy : 0 < y) :
    ∃ M : CrossIndex → ℝ, Summable M ∧
      ∀ (z : ℍ), z.im = y → |z.re| ≤ 1 → ∀ i, ‖actualCrossPhase z i * oddCrossSeed s z i‖ ≤ M i := by
  let K : ℝ := 2 + 18 / y ^ 2
  let C : ℝ := (y * K) ^ s.re * (2 : ℝ) ^ (-2 * s.re)
  let M : CrossIndex → ℝ := fun i => C * crossMajorant s.re (majorantIndex i)
  have hSummable : Summable M :=
    ((crossMajorant_summable hs).comp_injective majorantIndex_injective).mul_left C
  refine ⟨M, hSummable, fun z hY hX i => ?_⟩
  rcases i with ⟨D, A, n⟩
  have hHt : crossHeightConstant z ≤ K := by
    unfold crossHeightConstant K
    rw [hY]
    have hB : (|z.re| + 2) ^ 2 ≤ (3 : ℝ) ^ 2 := by
      gcongr <;> linarith
    have hSquare : 2 * (|z.re| + 2) ^ 2 ≤ 18 := by linarith
    exact add_le_add le_rfl (div_le_div_of_nonneg_right hSquare (sq_nonneg y))
  have hPow : (z.im * crossHeightConstant z) ^ s.re ≤ (y * K) ^ s.re := by
    rw [hY]
    exact Real.rpow_le_rpow (mul_nonneg hy.le (crossHeightConstant_pos z).le)
      (mul_le_mul_of_nonneg_left hHt hy.le) (by linarith)
  rw [norm_mul, actualCrossPhase_norm, one_mul]
  refine (oddCrossSeed_norm_le s z ⟨D, A, n⟩).trans ?_
  refine (scaledCross_rpow_le (by linarith) (Nat.succ_pos D) A z n).trans ?_
  unfold M C crossMajorant majorantIndex
  push_cast
  gcongr <;> unfold shiftMajorant <;> positivity

end
end ManuscriptAudit.Paper8OddCrossPoincareConvergence

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossPoincareConvergence.actualOddCrossSeries_summable
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
