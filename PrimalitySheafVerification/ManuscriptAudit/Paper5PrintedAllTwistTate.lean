import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenTwistPointCounts
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirteenTwistPointCounts
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenTwistPointCounts
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirtyOneTwists
import PrimalitySheafVerification.ManuscriptAudit.Paper5SplitTwistRows37To73
import PrimalitySheafVerification.ManuscriptAudit.Paper5SplitTwistRows79To109
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitAllPrimeAdic
import PrimalitySheafVerification.ManuscriptAudit.Paper5SplitTatePointCounts

/-! Native Tate point-count polynomials for every nonzero twist at every printed prime. -/

namespace ManuscriptAudit.Paper5PrintedAllTwistTate

open Polynomial Module PowerTateModule FiniteFieldPointCount
open CubicNonsplitThreeAdicTrace CubicNonsplitTwoThreeAdicCharpoly CubicThreePointCounts
open CubicSplitExtensionTraceRecurrence Paper5PrintedRecurrence Paper5SplitTwistCertificate
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

set_option maxHeartbeats 1200000

private theorem coefficient_prime {l : ℕ} (hl : l = 2 ∨ l = 3) : l.Prime := by
  rcases hl with rfl | rfl
  · exact Nat.prime_two
  · exact Nat.prime_three

private theorem lower_bound {r : Row} (hr : r ∈ printedRows) : 5 ≤ r.prime :=
  of_decide_eq_true (List.all_eq_true.mp
    (show printedRows.all (fun t => decide (5 ≤ t.prime)) = true by decide) r hr)

private theorem split_prime_list :
    (printedRows.filter (fun r => decide (r.prime % 3 ≠ 2))).map Row.prime =
      [7, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109] := by decide

abbrev action (p : ℕ) [Fact p.Prime] (L : Type*) [Field L] [Algebra (ZMod p) L]
    [IsAlgClosed L] [DecidableEq L] (l : ℕ) [Fact l.Prime] (A : ZMod p) :
    Module.End ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A)) :=
  endMap l (G := GeometricPoints (ZMod p) L A) (arithmeticPointFrobenius (ZMod p) L A)

private def correct (p : ℕ) [Fact p.Prime] (L : Type*) [Field L] [Algebra (ZMod p) L]
    [IsAlgClosed L] [DecidableEq L] (l : ℕ) [Fact l.Prime] (A : ZMod p) : Prop :=
  ∃ _ : Basis (Fin 2) ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A)),
    LinearMap.trace ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A)) (action p L l A) =
      (signedTrace A : ℤ_[l]) ∧ LinearMap.det (action p L l A) = (p : ℤ_[l])

private theorem correct_nonsplit {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hn : p % 3 = 2)
    (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) {A : ZMod p} (hA : A ≠ 0) :
    correct p L l A := by
  obtain ⟨h₂, h₃⟩ := Paper5NonsplitFrobeniusModFour.small_char p (ZMod p) hp
  have hq : Fintype.card (ZMod p) % 3 = 2 := by simpa only [ZMod.card] using hn
  have hS : signedTrace A = 0 := by
    rw [signedTrace, projective_count_residue_two A h₂ h₃ hA hq]
    simp [Nat.cast_add]
  have ht : LinearMap.trace ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A)) (action p L l A) =
      (signedTrace A : ℤ_[l]) := by
    rw [hS, Int.cast_zero]
    exact actual_prime_adic_trace_zero (ZMod p) L l h₂ h₃ hA hq
  rcases hl with rfl | rfl
  · exact ⟨twoAdicBasis (ZMod p) L h₂ h₃ hA, ht,
      by simpa only [ZMod.card] using two_adic_determinant (ZMod p) L h₂ h₃ hA hq⟩
  · exact ⟨threeAdicBasis (ZMod p) L h₂ h₃ hA, ht,
      by simpa only [ZMod.card] using three_adic_determinant (ZMod p) L h₂ h₃ hA hq⟩

private theorem correct_split {p : ℕ} [primeRow : Fact p.Prime]
    (hp : p ∈ ([7, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109] : List ℕ))
    (L : Type*) [Field L] [algebraRow : Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) {A : ZMod p} (hA : A ≠ 0) :
    correct p L l A := by
  letI charRow : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · letI : Algebra (ZMod 7) L := algebraRow
    letI : CharP L 7 := charRow
    letI : Fact (Nat.Prime 7) := primeRow
    have ht : LinearMap.trace ℤ_[l] (Tate l (GeometricPoints (ZMod 7) L A)) (action 7 L l A) =
        (signedTrace A : ℤ_[l]) := by
      have hc : signedTrace A =
          (8 : ℤ) - (Nat.card (paper5TraceCurve 7 A).toProjective.Point : ℤ) := by
        rw [signedTrace, ZMod.card, paper_curve_eq] <;> norm_num
      rw [hc]
      exact Paper5OrdinarySevenTwistPointCounts.actual_trace_eq_signed_count L l hl A hA
    exact ⟨Paper5OrdinarySevenTwistTate.tateBasis L l hl A hA, ht,
      (Paper5OrdinarySevenTwistTate.trace_det L l hl A hA).2⟩
  · letI : Algebra (ZMod 13) L := algebraRow
    letI : CharP L 13 := charRow
    letI : Fact (Nat.Prime 13) := primeRow
    have ht : LinearMap.trace ℤ_[l] (Tate l (GeometricPoints (ZMod 13) L A)) (action 13 L l A) =
        (signedTrace A : ℤ_[l]) := by
      have hc : signedTrace A =
          (14 : ℤ) - (Nat.card (paper5TraceCurve 13 A).toProjective.Point : ℤ) := by
        rw [signedTrace, ZMod.card, paper_curve_eq] <;> norm_num
      rw [hc]
      exact Paper5OrdinaryThirteenTwistPointCounts.actual_trace_eq_signed_count L l hl A hA
    exact ⟨Paper5OrdinaryThirteenTwistTate.tateBasis L l hl A hA, ht,
      (Paper5OrdinaryThirteenTwistTate.trace_det L l hl A hA).2⟩
  · letI : Algebra (ZMod 19) L := algebraRow
    letI : CharP L 19 := charRow
    letI : Fact (Nat.Prime 19) := primeRow
    have ht : LinearMap.trace ℤ_[l] (Tate l (GeometricPoints (ZMod 19) L A)) (action 19 L l A) =
        (signedTrace A : ℤ_[l]) := by
      have hc : signedTrace A =
          (20 : ℤ) - (Nat.card (paper5TraceCurve 19 A).toProjective.Point : ℤ) := by
        rw [signedTrace, ZMod.card, paper_curve_eq] <;> norm_num
      rw [hc]
      exact Paper5OrdinaryNineteenTwistPointCounts.actual_trace_eq_signed_count L l hl A hA
    exact ⟨Paper5OrdinaryNineteenTwistTate.tateBasis L l hl A hA, ht,
      (Paper5OrdinaryNineteenTwistTate.trace_det L l hl A hA).2⟩
  · letI : Algebra (ZMod 31) L := algebraRow
    letI : CharP L 31 := charRow
    letI : Fact (Nat.Prime 31) := primeRow
    exact ⟨Paper5OrdinaryThirtyOneTwists.basis L l hl hA,
      Paper5OrdinaryThirtyOneTwists.trace_det L l hl hA⟩
  · letI : Algebra (ZMod 37) L := algebraRow
    letI : CharP L 37 := charRow
    letI : Fact (Nat.Prime 37) := primeRow
    exact ⟨Paper5CertifiedSplitTwistTate.basis Paper5SplitTwistRows37To73.at37 L l hl hA,
      Paper5CertifiedSplitTwistTate.trace_det Paper5SplitTwistRows37To73.at37 L l
        (Paper5SplitTwistRows37To73.native37 L) hl hA⟩
  · letI : Algebra (ZMod 43) L := algebraRow
    letI : CharP L 43 := charRow
    letI : Fact (Nat.Prime 43) := primeRow
    exact ⟨Paper5CertifiedSplitTwistTate.basis Paper5SplitTwistRows37To73.at43 L l hl hA,
      Paper5CertifiedSplitTwistTate.trace_det Paper5SplitTwistRows37To73.at43 L l
        (Paper5SplitTwistRows37To73.native43 L) hl hA⟩
  · letI : Algebra (ZMod 61) L := algebraRow
    letI : CharP L 61 := charRow
    letI : Fact (Nat.Prime 61) := primeRow
    exact ⟨Paper5CertifiedSplitTwistTate.basis Paper5SplitTwistRows37To73.at61 L l hl hA,
      Paper5CertifiedSplitTwistTate.trace_det Paper5SplitTwistRows37To73.at61 L l
        (Paper5SplitTwistRows37To73.native61 L) hl hA⟩
  · letI : Algebra (ZMod 67) L := algebraRow
    letI : CharP L 67 := charRow
    letI : Fact (Nat.Prime 67) := primeRow
    exact ⟨Paper5CertifiedSplitTwistTate.basis Paper5SplitTwistRows37To73.at67 L l hl hA,
      Paper5CertifiedSplitTwistTate.trace_det Paper5SplitTwistRows37To73.at67 L l
        (Paper5SplitTwistRows37To73.native67 L) hl hA⟩
  · letI : Algebra (ZMod 73) L := algebraRow
    letI : CharP L 73 := charRow
    letI : Fact (Nat.Prime 73) := primeRow
    exact ⟨Paper5CertifiedSplitTwistTate.basis Paper5SplitTwistRows37To73.at73 L l hl hA,
      Paper5CertifiedSplitTwistTate.trace_det Paper5SplitTwistRows37To73.at73 L l
        (Paper5SplitTwistRows37To73.native73 L) hl hA⟩
  · letI : Algebra (ZMod 79) L := algebraRow
    letI : CharP L 79 := charRow
    letI : Fact (Nat.Prime 79) := primeRow
    exact ⟨Paper5CertifiedSplitTwistTate.basis Paper5SplitTwistRows79To109.at79 L l hl hA,
      Paper5CertifiedSplitTwistTate.trace_det Paper5SplitTwistRows79To109.at79 L l
        (Paper5SplitTwistRows79To109.native79 L) hl hA⟩
  · letI : Algebra (ZMod 97) L := algebraRow
    letI : CharP L 97 := charRow
    letI : Fact (Nat.Prime 97) := primeRow
    exact ⟨Paper5CertifiedSplitTwistTate.basis Paper5SplitTwistRows79To109.at97 L l hl hA,
      Paper5CertifiedSplitTwistTate.trace_det Paper5SplitTwistRows79To109.at97 L l
        (Paper5SplitTwistRows79To109.native97 L) hl hA⟩
  · letI : Algebra (ZMod 103) L := algebraRow
    letI : CharP L 103 := charRow
    letI : Fact (Nat.Prime 103) := primeRow
    exact ⟨Paper5CertifiedSplitTwistTate.basis Paper5SplitTwistRows79To109.at103 L l hl hA,
      Paper5CertifiedSplitTwistTate.trace_det Paper5SplitTwistRows79To109.at103 L l
        (Paper5SplitTwistRows79To109.native103 L) hl hA⟩
  · letI : Algebra (ZMod 109) L := algebraRow
    letI : CharP L 109 := charRow
    letI : Fact (Nat.Prime 109) := primeRow
    exact ⟨Paper5CertifiedSplitTwistTate.basis Paper5SplitTwistRows79To109.at109 L l hl hA,
      Paper5CertifiedSplitTwistTate.trace_det Paper5SplitTwistRows79To109.at109 L l
        (Paper5SplitTwistRows79To109.native109 L) hl hA⟩

/-- All printed primes and all nonzero coefficients have the exact native arithmetic trace and determinant. -/
theorem all_printed_twist_coefficients {r : Row} (hr : r ∈ printedRows)
    (L : Type*) [Field L] [Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]
    (l : ℕ) (hl : l = 2 ∨ l = 3) {A : ZMod r.prime} (hA : A ≠ 0) :
    letI : Fact r.prime.Prime := ⟨printedRows_prime hr⟩
    letI : Fact l.Prime := ⟨coefficient_prime hl⟩
    ∃ _ : Basis (Fin 2) ℤ_[l] (Tate l (GeometricPoints (ZMod r.prime) L A)),
      LinearMap.trace ℤ_[l] (Tate l (GeometricPoints (ZMod r.prime) L A)) (action r.prime L l A) =
        (signedTrace A : ℤ_[l]) ∧ LinearMap.det (action r.prime L l A) = (r.prime : ℤ_[l]) := by
  letI : Fact r.prime.Prime := ⟨printedRows_prime hr⟩
  letI : Fact l.Prime := ⟨coefficient_prime hl⟩
  by_cases hn : r.prime % 3 = 2
  · exact correct_nonsplit (lower_bound hr) hn L l hl hA
  · have h : r.prime ∈ (printedRows.filter (fun t => decide (t.prime % 3 ≠ 2))).map Row.prime :=
      List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simpa using hn⟩, rfl⟩
    rw [split_prime_list] at h
    exact correct_split h L l hl hA

/-- The exact arithmetic characteristic polynomial on the native rank-two Tate module. -/
theorem all_printed_twist_charpoly {r : Row} (hr : r ∈ printedRows)
    (L : Type*) [Field L] [Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]
    (l : ℕ) (hl : l = 2 ∨ l = 3) {A : ZMod r.prime} (hA : A ≠ 0) :
    letI : Fact r.prime.Prime := ⟨printedRows_prime hr⟩
    letI : Fact l.Prime := ⟨coefficient_prime hl⟩
    ∃ B : Basis (Fin 2) ℤ_[l] (Tate l (GeometricPoints (ZMod r.prime) L A)),
      letI := Module.Free.of_basis B
      letI := Module.Finite.of_basis B
      (action r.prime L l A).charpoly =
        X ^ 2 - C (signedTrace A : ℤ_[l]) * X + C (r.prime : ℤ_[l]) := by
  letI : Fact r.prime.Prime := ⟨printedRows_prime hr⟩
  letI : Fact l.Prime := ⟨coefficient_prime hl⟩
  obtain ⟨B, ht, hd⟩ := all_printed_twist_coefficients hr L l hl hA
  refine ⟨B, ?_⟩
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  change (action r.prime L l A).charpoly = _
  rw [← LinearMap.charpoly_toMatrix (action r.prime L l A) B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[l] B, LinearMap.det_toMatrix B, ht, hd]

/-- Every actual extension count equals the corresponding Frobenius power trace. -/
theorem all_printed_twist_extension_trace {r : Row} (hr : r ∈ printedRows)
    (L E : Type*) [Field L] [Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]
    [Algebra.IsAlgebraic (ZMod r.prime) L] [Field E] [Fintype E] [DecidableEq E]
    [Algebra (ZMod r.prime) E] (l : ℕ) (hl : l = 2 ∨ l = 3)
    {A : ZMod r.prime} (hA : A ≠ 0) :
    letI : Fact r.prime.Prime := ⟨printedRows_prime hr⟩
    letI : Fact l.Prime := ⟨coefficient_prime hl⟩
    LinearMap.trace ℤ_[l] (Tate l (GeometricPoints (ZMod r.prime) L A))
      (action r.prime L l A ^ Module.finrank (ZMod r.prime) E) =
    (((Fintype.card E : ℤ) + 1 -
      (Nat.card ((paper5TraceCurve r.prime A).baseChange E).toProjective.Point : ℤ) : ℤ) : ℤ_[l]) := by
  letI : Fact r.prime.Prime := ⟨printedRows_prime hr⟩
  letI : Fact l.Prime := ⟨coefficient_prime hl⟩
  have hp := lower_bound hr
  by_cases hn : r.prime % 3 = 2
  · have hlp : l ≠ r.prime := by rcases hl with rfl | rfl <;> omega
    simpa only [Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_one] using
      Paper5NonsplitAllPrimeAdic.trace_pow_eq_point_count r.prime L l hp hn hlp E hA
  · have h3 : r.prime % 3 ≠ 0 := by
      intro he
      have h := (Nat.dvd_prime (printedRows_prime hr)).mp (Nat.dvd_iff_mod_eq_zero.mpr he)
      rcases h with h | h <;> omega
    have hs : r.prime % 3 = 1 := by omega
    obtain ⟨B, ht, hd⟩ := all_printed_twist_coefficients hr L l hl hA
    exact Paper5SplitTatePointCounts.trace_power_eq_extension_count (p := r.prime) (E := E)
      hp hs hA B (action r.prime L l A)
      (by simpa only [signedTrace, ZMod.card, paper_curve_eq] using ht) hd

end
end ManuscriptAudit.Paper5PrintedAllTwistTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5PrintedAllTwistTate.all_printed_twist_coefficients,
      ``ManuscriptAudit.Paper5PrintedAllTwistTate.all_printed_twist_charpoly,
      ``ManuscriptAudit.Paper5PrintedAllTwistTate.all_printed_twist_extension_trace] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
