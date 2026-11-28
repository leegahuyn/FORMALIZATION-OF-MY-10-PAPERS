import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassDivisorClassSplit
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAffinePicard

/-! The geometric divisor-class Tate module is the genuine elliptic point
Tate module. The primitive degree summand contributes no finite torsion. -/

namespace ManuscriptAudit.WeierstrassDivisorClassTate

open WeierstrassCurve.Affine WeierstrassDivisorDegree WeierstrassDivisorClassSplit
open WeierstrassAffinePicard PowerTateModule PowerTorsionTower TorsionFrobeniusModule

noncomputable section

variable (l : ℕ) [Fact l.Prime]
variable (G : Type*) [AddCommGroup G]

private theorem zero_degree_of_powerTorsion (n : ℕ) (x : PowerTorsion l (G × ℤ) n) :
    x.val.2 = 0 := by
  have h : (l ^ n) • x.val = 0 := x.property
  have hz := congrArg Prod.snd h
  change (l ^ n) • x.val.2 = (0 : ℤ) at hz
  rw [nsmul_eq_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left (Nat.cast_ne_zero.mpr
    (pow_ne_zero n (Fact.out : Nat.Prime l).ne_zero))

/-- The actual compatible system of prime-power torsion ignores an
integer degree factor because each of its integer coordinates is zero. -/
def degreeFreeTate : Tate l (G × ℤ) ≃ₗ[ℤ_[l]] Tate l G := by
  let f : G × ℤ →+ G := AddMonoidHom.fst _ _
  let g : G →+ G × ℤ := AddMonoidHom.inl _ _
  refine LinearEquiv.ofBijective (PowerTateModule.map l f) ⟨?_, ?_⟩
  · intro x y h
    apply PowerTateModule.ext l (G × ℤ)
    intro n
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z : Tate l G => (evaluate l G n z).val) h
    · exact (zero_degree_of_powerTorsion l G n (evaluate l (G × ℤ) n x)).trans
        (zero_degree_of_powerTorsion l G n (evaluate l (G × ℤ) n y)).symm
  · intro x
    refine ⟨PowerTateModule.map l g x, ?_⟩
    apply PowerTateModule.ext l G
    intro n
    apply Subtype.ext
    rfl

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private def additiveProduct :
    Additive (ClassGroup W.CoordinateRing × Multiplicative ℤ) ≃+
      Additive (ClassGroup W.CoordinateRing) × ℤ where
  toFun x := (Additive.ofMul x.toMul.1, x.toMul.2.toAdd)
  invFun x := Additive.ofMul (x.1.toMul, Multiplicative.ofAdd x.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The native divisor class group is the geometric point group together
with the integer degree. -/
def divisorClassPointEquiv : Additive (DivisorClassGroup W) ≃+ W.Point × ℤ :=
  ((classGroupSplit W).toAdditive.trans (additiveProduct W)).trans
    ((((ClassGroup.equivPic W.CoordinateRing).toAdditive).trans (pointPicardEquiv W).symm).prodCongr
      (AddEquiv.refl ℤ))

/-- Over the algebraically closed ground field the actual divisor-class
Tate module recovers the elliptic curve's genuine geometric Tate module. -/
def divisorClassTateEquiv :
    Tate l (Additive (DivisorClassGroup W)) ≃ₗ[ℤ_[l]] Tate l W.Point :=
  (PowerTateModule.mapAddEquiv l (divisorClassPointEquiv W)).trans (degreeFreeTate l W.Point)

end

end ManuscriptAudit.WeierstrassDivisorClassTate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassDivisorClassTate.divisorClassTateEquiv
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
