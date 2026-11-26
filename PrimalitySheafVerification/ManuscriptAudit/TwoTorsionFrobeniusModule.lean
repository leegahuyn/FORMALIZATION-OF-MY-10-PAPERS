import Lean.Util.CollectAxioms
import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.Fintype.Card
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFrobeniusFixed

/-!
# The actual F₂-module and Frobenius on points killed by two

The kernel of doubling is an additive subgroup with its native
ZMod-module structure. Additive maps restrict to linear maps on this
kernel, including extension of the base field and native Frobenius.
-/

namespace ManuscriptAudit.TwoTorsionFrobeniusModule

open WeierstrassCurve WeierstrassFrobeniusFixed

noncomputable section

variable (G : Type*) [AddCommGroup G]

def subgroup : AddSubgroup G :=
  (nsmulAddMonoidHom (2 : ℕ) : G →+ G).ker

abbrev TwoTorsion := ↥(subgroup G)

theorem mem_iff (P : G) : P ∈ subgroup G ↔ (2 : ℕ) • P = 0 :=
  Iff.rfl

instance twoTorsionModule : Module (ZMod 2) (TwoTorsion G) :=
  AddCommGroup.zmodModule fun P => Subtype.ext ((mem_iff G P).mp P.property)

/-- Compare the bundled subgroup to its actual underlying point subtype. -/
def carrierEquiv : TwoTorsion G ≃ {P : G // (2 : ℕ) • P = 0} where
  toFun P := ⟨P, (mem_iff G P).mp P.property⟩
  invFun P := ⟨P, (mem_iff G P).mpr P.property⟩
  left_inv P := Subtype.ext rfl
  right_inv P := Subtype.ext rfl

abbrev inclusion : TwoTorsion G →+ G := (subgroup G).subtype

theorem inclusion_injective : Function.Injective (inclusion G) := Subtype.val_injective

theorem in_image_iff (P : G) : (∃ v : TwoTorsion G, inclusion G v = P) ↔ (2 : ℕ) • P = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact (mem_iff G v).mp v.property
  · intro h
    exact ⟨⟨P, (mem_iff G P).mpr h⟩, rfl⟩

variable {G} {H : Type*} [AddCommGroup H]

def mapAdd (f : G →+ H) : TwoTorsion G →+ TwoTorsion H where
  toFun P := ⟨f P, (mem_iff H (f P)).mpr (by
    rw [← map_nsmul, (mem_iff G P).mp P.property, map_zero])⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' P Q := Subtype.ext (map_add f (P : G) (Q : G))

/-- Every additive map restricts to a linear map on the actual two-torsion. -/
def mapLinear (f : G →+ H) : TwoTorsion G →ₗ[ZMod 2] TwoTorsion H :=
  (mapAdd f).toZModLinearMap 2

theorem mapLinear_inclusion (f : G →+ H) (P : TwoTorsion G) :
    inclusion H (mapLinear f P) = f (inclusion G P) := rfl

theorem mapLinear_injective (f : G →+ H) (hf : Function.Injective f) :
    Function.Injective (mapLinear f) :=
  fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

section AcrossFields

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [DecidableEq L] [DecidableEq M]

/-- The native base-extension map of Weierstrass points restricted to two-torsion. -/
def pointMap (W : Affine K) (f : L →ₐ[K] M) :
    TwoTorsion (W.baseChange L).Point →ₗ[ZMod 2] TwoTorsion (W.baseChange M).Point :=
  mapLinear (Affine.Point.map (W' := W) f)

theorem pointMap_injective (W : Affine K) (f : L →ₐ[K] M) :
    Function.Injective (pointMap W f) :=
  mapLinear_injective _ (Affine.Point.map_injective (W' := W) f)

end AcrossFields

section Frobenius

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [DecidableEq L]
variable (W : Affine (ZMod p))

theorem frobeniusOnPoints_injective :
    Function.Injective (frobeniusOnPoints p L W) :=
  Affine.Point.map_injective (W' := W) (FiniteField.frobeniusAlgHom (ZMod p) L)

def frobeniusLinear :
    TwoTorsion (W.baseChange L).Point →ₗ[ZMod 2] TwoTorsion (W.baseChange L).Point :=
  mapLinear (frobeniusOnPoints p L W)

theorem frobeniusLinear_injective : Function.Injective (frobeniusLinear p L W) :=
  mapLinear_injective _ (frobeniusOnPoints_injective p L W)

/-- Injective native Frobenius is an automorphism on finite two-torsion. -/
def frobeniusLinearEquiv [Finite (TwoTorsion (W.baseChange L).Point)] :
    TwoTorsion (W.baseChange L).Point ≃ₗ[ZMod 2] TwoTorsion (W.baseChange L).Point :=
  LinearEquiv.ofBijective (frobeniusLinear p L W)
    (frobeniusLinear_injective p L W).bijective_of_finite

theorem frobeniusLinearEquiv_inclusion [Finite (TwoTorsion (W.baseChange L).Point)]
    (P : TwoTorsion (W.baseChange L).Point) :
    inclusion _ (frobeniusLinearEquiv p L W P) = frobeniusOnPoints p L W (inclusion _ P) :=
  rfl

end Frobenius

end

end ManuscriptAudit.TwoTorsionFrobeniusModule

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
    [``ManuscriptAudit.TwoTorsionFrobeniusModule.carrierEquiv,
      ``ManuscriptAudit.TwoTorsionFrobeniusModule.in_image_iff,
      ``ManuscriptAudit.TwoTorsionFrobeniusModule.pointMap_injective,
      ``ManuscriptAudit.TwoTorsionFrobeniusModule.frobeniusOnPoints_injective,
      ``ManuscriptAudit.TwoTorsionFrobeniusModule.frobeniusLinearEquiv_inclusion] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
