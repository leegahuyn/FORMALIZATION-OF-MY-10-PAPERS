import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5LaterNonsplitTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5LaterSmallSplitTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5LaterFirstSplitTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5LaterMidSplitTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5LaterHighSplitTate

/-! The later printed integer trace and determinant columns on the genuine Tate modules for A = 4. -/

namespace ManuscriptAudit.Paper5LaterAllTateCoefficients

open Paper5LaterTables PowerTateModule CubicFrobeniusSexticTwists

noncomputable section

private def splitRows : List TateRow :=
  [⟨4, 7, 5, 7, true⟩,
   ⟨6, 13, -7, 13, true⟩,
   ⟨8, 19, -1, 19, true⟩,
   ⟨11, 31, -4, 31, true⟩,
   ⟨12, 37, -1, 37, true⟩,
   ⟨14, 43, 8, 43, true⟩,
   ⟨18, 61, -13, 61, true⟩,
   ⟨19, 67, 11, 67, true⟩,
   ⟨21, 73, 17, 73, true⟩,
   ⟨22, 79, -13, 79, true⟩,
   ⟨25, 97, 5, 97, true⟩,
   ⟨27, 103, -7, 103, true⟩,
   ⟨29, 109, 2, 109, true⟩]

theorem split_rows_exact :
    tateRows.filter (fun r => decide (r.prime % 3 ≠ 2)) = splitRows := by decide

private theorem row_primes : ∀ r ∈ tateRows, r.prime.Prime ∧ 5 ≤ r.prime := by decide

private theorem coefficient_prime {l : ℕ} (hl : l = 2 ∨ l = 3) : l.Prime := by
  rcases hl with rfl | rfl <;> decide

theorem trace_det {r : TateRow} (hr : r ∈ tateRows)
    (L : Type*) [Field L] [algebraRow : Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]
    (l : ℕ) (hl : l = 2 ∨ l = 3) :
    letI : Fact r.prime.Prime := ⟨(row_primes r hr).1⟩
    letI : Fact l.Prime := ⟨coefficient_prime hl⟩
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod r.prime) L 4))
      (endMap l (arithmeticFrobenius (ZMod r.prime) L 4)) = (r.trace : ℤ_[l]) ∧
    LinearMap.det (endMap l (arithmeticFrobenius (ZMod r.prime) L 4)) =
      (r.determinant : ℤ_[l]) := by
  letI primeRow : Fact r.prime.Prime := ⟨(row_primes r hr).1⟩
  letI : Fact l.Prime := ⟨coefficient_prime hl⟩
  dsimp only
  by_cases hn : r.prime % 3 = 2
  · obtain ⟨hT, hD⟩ := Paper5LaterNonsplitTate.data_exact r hr hn
    rw [hT, hD, Int.cast_zero]
    exact Paper5LaterNonsplitTate.trace_det_nonsplit r.prime L (row_primes r hr).2 hn l hl
  · have h : r ∈ splitRows := by
      rw [← split_rows_exact]
      exact List.mem_filter.mpr ⟨hr, by simp [hn]⟩
    letI charRow : CharP L r.prime :=
      charP_of_injective_algebraMap (algebraMap (ZMod r.prime) L).injective r.prime
    simp only [splitRows, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · letI : Algebra (ZMod 7) L := algebraRow
      letI : CharP L 7 := charRow
      norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_one]
      exact Paper5LaterSmallSplitTate.trace_det_7 L l hl
    · letI : Algebra (ZMod 13) L := algebraRow
      letI : CharP L 13 := charRow
      norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_one]
      exact Paper5LaterSmallSplitTate.trace_det_13 L l hl
    · letI : Algebra (ZMod 19) L := algebraRow
      letI : CharP L 19 := charRow
      norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_one]
      exact Paper5LaterSmallSplitTate.trace_det_19 L l hl
    · letI : Algebra (ZMod 31) L := algebraRow
      letI : CharP L 31 := charRow
      norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_one]
      exact Paper5LaterMidSplitTate.trace_det_31 L l hl
    · letI : Algebra (ZMod 37) L := algebraRow
      letI : CharP L 37 := charRow
      norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_one]
      exact Paper5LaterFirstSplitTate.trace_det_37 L l hl
    · letI : Algebra (ZMod 43) L := algebraRow
      letI : CharP L 43 := charRow
      norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_one]
      exact Paper5LaterMidSplitTate.trace_det_43 L l hl
    · letI : Algebra (ZMod 61) L := algebraRow
      letI : CharP L 61 := charRow
      norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_one]
      exact Paper5LaterFirstSplitTate.trace_det_61 L l hl
    · letI : Algebra (ZMod 67) L := algebraRow
      letI : CharP L 67 := charRow
      norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_one]
      exact Paper5LaterMidSplitTate.trace_det_67 L l hl
    · letI : Algebra (ZMod 73) L := algebraRow
      letI : CharP L 73 := charRow
      norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_one]
      exact Paper5LaterMidSplitTate.trace_det_73 L l hl
    · letI : Algebra (ZMod 79) L := algebraRow
      letI : CharP L 79 := charRow
      norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_one]
      exact Paper5LaterHighSplitTate.trace_det_79 L l hl
    · letI : Algebra (ZMod 97) L := algebraRow
      letI : CharP L 97 := charRow
      norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_one]
      exact Paper5LaterHighSplitTate.trace_det_97 L l hl
    · letI : Algebra (ZMod 103) L := algebraRow
      letI : CharP L 103 := charRow
      norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_one]
      exact Paper5LaterHighSplitTate.trace_det_103 L l hl
    · letI : Algebra (ZMod 109) L := algebraRow
      letI : CharP L 109 := charRow
      norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_one]
      exact Paper5LaterHighSplitTate.trace_det_109 L l hl

end
end ManuscriptAudit.Paper5LaterAllTateCoefficients

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5LaterAllTateCoefficients.split_rows_exact,
      ``ManuscriptAudit.Paper5LaterAllTateCoefficients.trace_det] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
