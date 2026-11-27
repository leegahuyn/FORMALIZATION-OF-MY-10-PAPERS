import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5CertifiedSplitTwistTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySeventyNineFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNinetySevenFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryOneHundredThreeFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryOneHundredNineFrobenius

/-! Kernel-checked sextic twist representatives and certified point-group Frobenius of these split primes. -/

namespace ManuscriptAudit.Paper5SplitTwistRows79To109

open Paper5SplitTwistCertificate Paper5CertifiedSplitTwistTate

noncomputable section

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

local instance : Fact (Nat.Prime 79) := ⟨by decide⟩

def at79 : Certificate 79 where
  k := 13
  z := 55
  a := 3
  b := 10
  representative := ![1, 2, 3, 4, 6, 12]
  lower := by decide
  card := by decide
  primitive := IsPrimitiveRoot.iff_orderOf.mpr
    ((orderOf_eq_prime_iff (p := 3)).mpr ⟨by decide, by decide⟩)
  norm := by decide
  cover := by decide
  check := by decide

theorem native79 (L : Type*) [Field L] [Algebra (ZMod 79) L] [CharP L 79]
    [IsAlgClosed L] [DecidableEq L] : IsNativeReference at79 L := by
  change Paper5OrdinarySeventyNineFrobenius.nativeFrobenius L =
    (3 : ℤ) • (1 : AddMonoid.End (Paper5OrdinarySeventyNineFrobenius.Points L)) +
      (10 : ℤ) • Paper5OrdinarySeventyNineFrobenius.rotation L
  simpa only [ofNat_zsmul, one_zsmul, neg_zsmul, sub_eq_add_neg, one_nsmul] using
    Paper5OrdinarySeventyNineFrobenius.native_eq_rotation L

local instance : Fact (Nat.Prime 97) := ⟨by decide⟩

def at97 : Certificate 97 where
  k := 16
  z := 61
  a := 3
  b := -8
  representative := ![1, 2, 4, 5, 10, 19]
  lower := by decide
  card := by decide
  primitive := IsPrimitiveRoot.iff_orderOf.mpr
    ((orderOf_eq_prime_iff (p := 3)).mpr ⟨by decide, by decide⟩)
  norm := by decide
  cover := by decide
  check := by decide

theorem native97 (L : Type*) [Field L] [Algebra (ZMod 97) L] [CharP L 97]
    [IsAlgClosed L] [DecidableEq L] : IsNativeReference at97 L := by
  change Paper5OrdinaryNinetySevenFrobenius.nativeFrobenius L =
    (3 : ℤ) • (1 : AddMonoid.End (Paper5OrdinaryNinetySevenFrobenius.Points L)) +
      (-8 : ℤ) • Paper5OrdinaryNinetySevenFrobenius.rotation L
  simpa only [ofNat_zsmul, one_zsmul, neg_zsmul, sub_eq_add_neg, one_nsmul] using
    Paper5OrdinaryNinetySevenFrobenius.native_eq_rotation L

local instance : Fact (Nat.Prime 103) := ⟨by decide⟩

def at103 : Certificate 103 where
  k := 17
  z := 56
  a := 9
  b := -2
  representative := ![1, 2, 3, 4, 5, 6]
  lower := by decide
  card := by decide
  primitive := IsPrimitiveRoot.iff_orderOf.mpr
    ((orderOf_eq_prime_iff (p := 3)).mpr ⟨by decide, by decide⟩)
  norm := by decide
  cover := by decide
  check := by decide

theorem native103 (L : Type*) [Field L] [Algebra (ZMod 103) L] [CharP L 103]
    [IsAlgClosed L] [DecidableEq L] : IsNativeReference at103 L := by
  change Paper5OrdinaryOneHundredThreeFrobenius.nativeFrobenius L =
    (9 : ℤ) • (1 : AddMonoid.End (Paper5OrdinaryOneHundredThreeFrobenius.Points L)) +
      (-2 : ℤ) • Paper5OrdinaryOneHundredThreeFrobenius.rotation L
  simpa only [ofNat_zsmul, one_zsmul, neg_zsmul, sub_eq_add_neg, one_nsmul] using
    Paper5OrdinaryOneHundredThreeFrobenius.native_eq_rotation L

local instance : Fact (Nat.Prime 109) := ⟨by decide⟩

def at109 : Certificate 109 where
  k := 18
  z := 45
  a := -5
  b := -12
  representative := ![1, 2, 3, 6, 9, 11]
  lower := by decide
  card := by decide
  primitive := IsPrimitiveRoot.iff_orderOf.mpr
    ((orderOf_eq_prime_iff (p := 3)).mpr ⟨by decide, by decide⟩)
  norm := by decide
  cover := by decide
  check := by decide

theorem native109 (L : Type*) [Field L] [Algebra (ZMod 109) L] [CharP L 109]
    [IsAlgClosed L] [DecidableEq L] : IsNativeReference at109 L := by
  change Paper5OrdinaryOneHundredNineFrobenius.nativeFrobenius L =
    (-5 : ℤ) • (1 : AddMonoid.End (Paper5OrdinaryOneHundredNineFrobenius.Points L)) +
      (-12 : ℤ) • Paper5OrdinaryOneHundredNineFrobenius.rotation L
  simpa only [ofNat_zsmul, one_zsmul, neg_zsmul, sub_eq_add_neg, one_nsmul] using
    Paper5OrdinaryOneHundredNineFrobenius.native_eq_rotation L

end
end ManuscriptAudit.Paper5SplitTwistRows79To109

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5SplitTwistRows79To109.at79,
      ``ManuscriptAudit.Paper5SplitTwistRows79To109.native79,
      ``ManuscriptAudit.Paper5SplitTwistRows79To109.at97,
      ``ManuscriptAudit.Paper5SplitTwistRows79To109.native97,
      ``ManuscriptAudit.Paper5SplitTwistRows79To109.at103,
      ``ManuscriptAudit.Paper5SplitTwistRows79To109.native103,
      ``ManuscriptAudit.Paper5SplitTwistRows79To109.at109,
      ``ManuscriptAudit.Paper5SplitTwistRows79To109.native109] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
