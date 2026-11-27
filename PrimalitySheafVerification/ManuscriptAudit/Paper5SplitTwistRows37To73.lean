import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5CertifiedSplitTwistTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirtySevenFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryFortyThreeFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySixtyOneFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySixtySevenFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySeventyThreeFrobenius

/-! Kernel-checked sextic twist representatives and certified point-group Frobenius of these split primes. -/

namespace ManuscriptAudit.Paper5SplitTwistRows37To73

open Paper5SplitTwistCertificate Paper5CertifiedSplitTwistTate

noncomputable section

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

def at37 : Certificate 37 where
  k := 6
  z := 10
  a := -3
  b := 4
  representative := ![1, 2, 3, 5, 6, 9]
  lower := by decide
  card := by decide
  primitive := IsPrimitiveRoot.iff_orderOf.mpr
    ((orderOf_eq_prime_iff (p := 3)).mpr ⟨by decide, by decide⟩)
  norm := by decide
  cover := by decide
  check := by decide

theorem native37 (L : Type*) [Field L] [Algebra (ZMod 37) L] [CharP L 37]
    [IsAlgClosed L] [DecidableEq L] : IsNativeReference at37 L := by
  change Paper5OrdinaryThirtySevenFrobenius.nativeFrobenius L =
    (-3 : ℤ) • (1 : AddMonoid.End (Paper5OrdinaryThirtySevenFrobenius.Points L)) +
      (4 : ℤ) • Paper5OrdinaryThirtySevenFrobenius.rotation L
  simpa only [ofNat_zsmul, one_zsmul, neg_zsmul, sub_eq_add_neg, one_nsmul] using
    Paper5OrdinaryThirtySevenFrobenius.native_eq_rotation L

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩

def at43 : Certificate 43 where
  k := 7
  z := 36
  a := 1
  b := -6
  representative := ![1, 2, 3, 6, 7, 9]
  lower := by decide
  card := by decide
  primitive := IsPrimitiveRoot.iff_orderOf.mpr
    ((orderOf_eq_prime_iff (p := 3)).mpr ⟨by decide, by decide⟩)
  norm := by decide
  cover := by decide
  check := by decide

theorem native43 (L : Type*) [Field L] [Algebra (ZMod 43) L] [CharP L 43]
    [IsAlgClosed L] [DecidableEq L] : IsNativeReference at43 L := by
  change Paper5OrdinaryFortyThreeFrobenius.nativeFrobenius L =
    (1 : ℤ) • (1 : AddMonoid.End (Paper5OrdinaryFortyThreeFrobenius.Points L)) +
      (-6 : ℤ) • Paper5OrdinaryFortyThreeFrobenius.rotation L
  simpa only [ofNat_zsmul, one_zsmul, neg_zsmul, sub_eq_add_neg, one_nsmul] using
    Paper5OrdinaryFortyThreeFrobenius.native_eq_rotation L

local instance : Fact (Nat.Prime 61) := ⟨by decide⟩

def at61 : Certificate 61 where
  k := 10
  z := 47
  a := 5
  b := -4
  representative := ![1, 2, 4, 5, 8, 10]
  lower := by decide
  card := by decide
  primitive := IsPrimitiveRoot.iff_orderOf.mpr
    ((orderOf_eq_prime_iff (p := 3)).mpr ⟨by decide, by decide⟩)
  norm := by decide
  cover := by decide
  check := by decide

theorem native61 (L : Type*) [Field L] [Algebra (ZMod 61) L] [CharP L 61]
    [IsAlgClosed L] [DecidableEq L] : IsNativeReference at61 L := by
  change Paper5OrdinarySixtyOneFrobenius.nativeFrobenius L =
    (5 : ℤ) • (1 : AddMonoid.End (Paper5OrdinarySixtyOneFrobenius.Points L)) +
      (-4 : ℤ) • Paper5OrdinarySixtyOneFrobenius.rotation L
  simpa only [ofNat_zsmul, one_zsmul, neg_zsmul, sub_eq_add_neg, one_nsmul] using
    Paper5OrdinarySixtyOneFrobenius.native_eq_rotation L

local instance : Fact (Nat.Prime 67) := ⟨by decide⟩

def at67 : Certificate 67 where
  k := 11
  z := 29
  a := -9
  b := -2
  representative := ![1, 2, 3, 4, 6, 7]
  lower := by decide
  card := by decide
  primitive := IsPrimitiveRoot.iff_orderOf.mpr
    ((orderOf_eq_prime_iff (p := 3)).mpr ⟨by decide, by decide⟩)
  norm := by decide
  cover := by decide
  check := by decide

theorem native67 (L : Type*) [Field L] [Algebra (ZMod 67) L] [CharP L 67]
    [IsAlgClosed L] [DecidableEq L] : IsNativeReference at67 L := by
  change Paper5OrdinarySixtySevenFrobenius.nativeFrobenius L =
    (-9 : ℤ) • (1 : AddMonoid.End (Paper5OrdinarySixtySevenFrobenius.Points L)) +
      (-2 : ℤ) • Paper5OrdinarySixtySevenFrobenius.rotation L
  simpa only [ofNat_zsmul, one_zsmul, neg_zsmul, sub_eq_add_neg, one_nsmul] using
    Paper5OrdinarySixtySevenFrobenius.native_eq_rotation L

local instance : Fact (Nat.Prime 73) := ⟨by decide⟩

def at73 : Certificate 73 where
  k := 12
  z := 64
  a := -1
  b := 8
  representative := ![1, 2, 4, 5, 7, 13]
  lower := by decide
  card := by decide
  primitive := IsPrimitiveRoot.iff_orderOf.mpr
    ((orderOf_eq_prime_iff (p := 3)).mpr ⟨by decide, by decide⟩)
  norm := by decide
  cover := by decide
  check := by decide

theorem native73 (L : Type*) [Field L] [Algebra (ZMod 73) L] [CharP L 73]
    [IsAlgClosed L] [DecidableEq L] : IsNativeReference at73 L := by
  change Paper5OrdinarySeventyThreeFrobenius.nativeFrobenius L =
    (-1 : ℤ) • (1 : AddMonoid.End (Paper5OrdinarySeventyThreeFrobenius.Points L)) +
      (8 : ℤ) • Paper5OrdinarySeventyThreeFrobenius.rotation L
  simpa only [ofNat_zsmul, one_zsmul, neg_zsmul, sub_eq_add_neg, one_nsmul] using
    Paper5OrdinarySeventyThreeFrobenius.native_eq_rotation L

end
end ManuscriptAudit.Paper5SplitTwistRows37To73

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5SplitTwistRows37To73.at37,
      ``ManuscriptAudit.Paper5SplitTwistRows37To73.native37,
      ``ManuscriptAudit.Paper5SplitTwistRows37To73.at43,
      ``ManuscriptAudit.Paper5SplitTwistRows37To73.native43,
      ``ManuscriptAudit.Paper5SplitTwistRows37To73.at61,
      ``ManuscriptAudit.Paper5SplitTwistRows37To73.native61,
      ``ManuscriptAudit.Paper5SplitTwistRows37To73.at67,
      ``ManuscriptAudit.Paper5SplitTwistRows37To73.native67,
      ``ManuscriptAudit.Paper5SplitTwistRows37To73.at73,
      ``ManuscriptAudit.Paper5SplitTwistRows37To73.native73] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
